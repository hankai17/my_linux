/*
 *	IP multicast routing support for mrouted 3.6/3.8
 *
 *		(c) 1995 Alan Cox, <alan@redhat.com>
 *	  Linux Consultancy and Custom Driver Development
 *
 *	This program is free software; you can redistribute it and/or
 *	modify it under the terms of the GNU General Public License
 *	as published by the Free Software Foundation; either version
 *	2 of the License, or (at your option) any later version.
 *
 *	Version: $Id: ipmr.c,v 1.65 2001/10/31 21:55:54 davem Exp $
 *
 *	Fixes:
 *	Michael Chastain	:	Incorrect size of copying.
 *	Alan Cox		:	Added the cache manager code
 *	Alan Cox		:	Fixed the clone/copy bug and device race.
 *	Mike McLagan		:	Routing by source
 *	Malcolm Beattie		:	Buffer handling fixes.
 *	Alexey Kuznetsov	:	Double buffer free and other fixes.
 *	SVR Anand		:	Fixed several multicast bugs and problems.
 *	Alexey Kuznetsov	:	Status, optimisations and more.
 *	Brad Parker		:	Better behaviour on mrouted upcall
 *					overflow.
 *      Carlos Picoto           :       PIMv1 Support
 *	Pavlin Ivanov Radoslavov:	PIMv2 Registers must checksum only PIM header
 *					Relax this requrement to work with older peers.
 *
 */

#include <asm/system.h>
#include <asm/uaccess.h>
#include <linux/types.h>
#include <linux/sched.h>
#include <linux/capability.h>
#include <linux/errno.h>
#include <linux/timer.h>
#include <linux/mm.h>
#include <linux/kernel.h>
#include <linux/fcntl.h>
#include <linux/stat.h>
#include <linux/socket.h>
#include <linux/in.h>
#include <linux/inet.h>
#include <linux/netdevice.h>
#include <linux/inetdevice.h>
#include <linux/igmp.h>
#include <linux/proc_fs.h>
#include <linux/seq_file.h>
#include <linux/mroute.h>
#include <linux/init.h>
#include <linux/if_ether.h>
#include <net/ip.h>
#include <net/protocol.h>
#include <linux/skbuff.h>
#include <net/route.h>
#include <net/sock.h>
#include <net/icmp.h>
#include <net/udp.h>
#include <net/raw.h>
#include <linux/notifier.h>
#include <linux/if_arp.h>
#include <linux/netfilter_ipv4.h>
#include <net/ipip.h>
#include <net/checksum.h>

#if defined(CONFIG_IP_PIMSM_V1) || defined(CONFIG_IP_PIMSM_V2)
#define CONFIG_IP_PIMSM	1
#endif

static struct sock *mroute_socket;


/* Big lock, protecting vif table, mrt cache and mroute socket state.
   Note that the changes are semaphored via rtnl_lock.
 */

static DEFINE_RWLOCK(mrt_lock);

/*
 *	Multicast router control variables
 */

static struct vif_device vif_table[MAXVIFS];		/* Devices 		*/
static int maxvif;

#define VIF_EXISTS(idx) (vif_table[idx].dev != NULL)

static int mroute_do_assert;				/* Set in PIM assert	*/
static int mroute_do_pim;

static struct mfc_cache *mfc_cache_array[MFC_LINES];	/* Forwarding cache	*/

static struct mfc_cache *mfc_unres_queue;		/* Queue of unresolved entries */
static atomic_t cache_resolve_queue_len;		/* Size of unresolved	*/

/* Special spinlock for queue of unresolved entries */
static DEFINE_SPINLOCK(mfc_unres_lock);

/* We return to original Alan's scheme. Hash table of resolved
   entries is changed only in process context and protected
   with weak lock mrt_lock. Queue of unresolved entries is protected
   with strong spinlock mfc_unres_lock.

   In this case data path is free of exclusive locks at all.
 */

static struct kmem_cache *mrt_cachep __read_mostly;

static int ip_mr_forward(struct sk_buff *skb, struct mfc_cache *cache, int local);
static int ipmr_cache_report(struct sk_buff *pkt, vifi_t vifi, int assert);
static int ipmr_fill_mroute(struct sk_buff *skb, struct mfc_cache *c, struct rtmsg *rtm);

#ifdef CONFIG_IP_PIMSM_V2
static struct net_protocol pim_protocol;
#endif

static struct timer_list ipmr_expire_timer;

/* Service routines creating virtual interfaces: DVMRP tunnels and PIMREG */

static
struct net_device *ipmr_new_tunnel(struct vifctl *v)
{
	struct net_device  *dev;

	dev = __dev_get_by_name("tunl0");

	if (dev) {
		int err;
		struct ifreq ifr;
		mm_segment_t	oldfs;
		struct ip_tunnel_parm p;
		struct in_device  *in_dev;

		memset(&p, 0, sizeof(p));
		p.iph.daddr = v->vifc_rmt_addr.s_addr;
		p.iph.saddr = v->vifc_lcl_addr.s_addr;
		p.iph.version = 4;
		p.iph.ihl = 5;
		p.iph.protocol = IPPROTO_IPIP;
		sprintf(p.name, "dvmrp%d", v->vifc_vifi);
		ifr.ifr_ifru.ifru_data = (void*)&p;

		oldfs = get_fs(); set_fs(KERNEL_DS);
		err = dev->do_ioctl(dev, &ifr, SIOCADDTUNNEL);
		set_fs(oldfs);

		dev = NULL;

		if (err == 0 && (dev = __dev_get_by_name(p.name)) != NULL) {
			dev->flags |= IFF_MULTICAST;

			in_dev = __in_dev_get_rtnl(dev);
			if (in_dev == NULL && (in_dev = inetdev_init(dev)) == NULL)
				goto failure;
			in_dev->cnf.rp_filter = 0;

			if (dev_open(dev))
				goto failure;
		}
	}
	return dev;

failure:
	/* allow the register to be completed before unregistering. */
	rtnl_unlock();
	rtnl_lock();

	unregister_netdevice(dev);
	return NULL;
}

#ifdef CONFIG_IP_PIMSM

static int reg_vif_num = -1;

static int reg_vif_xmit(struct sk_buff *skb, struct net_device *dev)
{
	read_lock(&mrt_lock);
	((struct net_device_stats*)netdev_priv(dev))->tx_bytes += skb->len;
	((struct net_device_stats*)netdev_priv(dev))->tx_packets++;
	ipmr_cache_report(skb, reg_vif_num, IGMPMSG_WHOLEPKT);
	read_unlock(&mrt_lock);
	kfree_skb(skb);
	return 0;
}

static struct net_device_stats *reg_vif_get_stats(struct net_device *dev)
{
	return (struct net_device_stats*)netdev_priv(dev);
}

static void reg_vif_setup(struct net_device *dev)
{
	dev->type		= ARPHRD_PIMREG;
	dev->mtu		= ETH_DATA_LEN - sizeof(struct iphdr) - 8;
	dev->flags		= IFF_NOARP;
	dev->hard_start_xmit	= reg_vif_xmit;
	dev->get_stats		= reg_vif_get_stats;
	dev->destructor		= free_netdev;
}

static struct net_device *ipmr_reg_vif(void)
{
	struct net_device *dev;
	struct in_device *in_dev;

	dev = alloc_netdev(sizeof(struct net_device_stats), "pimreg",
			   reg_vif_setup);

	if (dev == NULL)
		return NULL;

	if (register_netdevice(dev)) {
		free_netdev(dev);
		return NULL;
	}
	dev->iflink = 0;

	if ((in_dev = inetdev_init(dev)) == NULL)
		goto failure;

	in_dev->cnf.rp_filter = 0;

	if (dev_open(dev))
		goto failure;

	return dev;

failure:
	/* allow the register to be completed before unregistering. */
	rtnl_unlock();
	rtnl_lock();

	unregister_netdevice(dev);
	return NULL;
}
#endif

/*
 *	Delete a VIF entry
 */
 
static int vif_delete(int vifi) //待删除虚拟接口的索引
{
	struct vif_device *v;
	struct net_device *dev;
	struct in_device *in_dev;

	if (vifi < 0 || vifi >= maxvif)
		return -EADDRNOTAVAIL;

	v = &vif_table[vifi];

	write_lock_bh(&mrt_lock);
	dev = v->dev;
	v->dev = NULL;

	if (!dev) {
		write_unlock_bh(&mrt_lock);
		return -EADDRNOTAVAIL;
	}

#ifdef CONFIG_IP_PIMSM
	if (vifi == reg_vif_num)
		reg_vif_num = -1;
#endif

	if (vifi+1 == maxvif) {
		int tmp;
		for (tmp=vifi-1; tmp>=0; tmp--) {
			if (VIF_EXISTS(tmp))
				break;
		}
		maxvif = tmp+1;
	}

	write_unlock_bh(&mrt_lock);

	dev_set_allmulti(dev, -1); //更新网卡的allmuti标志 取消该网卡的接收组播包功能

	if ((in_dev = __in_dev_get_rtnl(dev)) != NULL) { //更新网卡组播转发标志  //刷新路由
		in_dev->cnf.mc_forwarding--;
		ip_rt_multicast_event(in_dev);
	}

	if (v->flags&(VIFF_TUNNEL|VIFF_REGISTER)) //如果是viff_tunnel或viff_register类型的虚拟接口 则先创建网卡
		unregister_netdevice(dev);

	dev_put(dev);
	return 0;
}

/* Destroy an unresolved cache entry, killing queued skbs
   and reporting error to netlink readers.
 */

static void ipmr_destroy_unres(struct mfc_cache *c)
{
	struct sk_buff *skb;
	struct nlmsgerr *e;

	atomic_dec(&cache_resolve_queue_len); //递减临时组播转发缓存队列长度

	while((skb=skb_dequeue(&c->mfc_un.unres.unresolved))) { //遍历待释放临时组播转发缓存项中保存的组播报文 如果该报文是用户进程通过netlink方式获取组播路由信息的报文 则报告NLMSG_ERROR错误 否则释放该组播报文
		if (skb->nh.iph->version == 0) {
			struct nlmsghdr *nlh = (struct nlmsghdr *)skb_pull(skb, sizeof(struct iphdr));
			nlh->nlmsg_type = NLMSG_ERROR;
			nlh->nlmsg_len = NLMSG_LENGTH(sizeof(struct nlmsgerr));
			skb_trim(skb, nlh->nlmsg_len);
			e = NLMSG_DATA(nlh);
			e->error = -ETIMEDOUT;
			memset(&e->msg, 0, sizeof(e->msg));

			rtnl_unicast(skb, NETLINK_CB(skb).pid);
		} else
			kfree_skb(skb);
	}

	kmem_cache_free(mrt_cachep, c); //释放该临时组播转发缓存项
}


/* Single timer process for all the unresolved queue. */

static void ipmr_expire_process(unsigned long dummy) //ipmr_cache_unresolved创建新的临时转发路由缓存项后 发送IGMPMSG_NOCACHE给组播路由守护进程 接着启动定时器 如果在该定时器到期仍未处理该缓存项 则调此函数
{
	unsigned long now;
	unsigned long expires;
	struct mfc_cache *c, **cp;

	if (!spin_trylock(&mfc_unres_lock)) { //如果当前临时组播转发缓存队列正被访问 则只能重新设置定时器后返回 稍后处理
		mod_timer(&ipmr_expire_timer, jiffies+HZ/10);
		return;
	}

	if (atomic_read(&cache_resolve_queue_len) == 0) //临时组播转发缓存队列长度为0 无需处理
		goto out;

	now = jiffies; //清除已超时的临时组播转发缓存项
	expires = 10*HZ;
	cp = &mfc_unres_queue;

	while ((c=*cp) != NULL) { //遍历临时组播转发缓存队列
		if (time_after(c->mfc_un.unres.expires, now)) { //获取临时组播转发缓存队列中所有未超时缓存项所剩超时时间的最小值 用于之后设置ipmr_expire_timer值
			unsigned long interval = c->mfc_un.unres.expires - now;
			if (interval < expires)
				expires = interval;
			cp = &c->next;
			continue;
		}

		*cp = c->next;

		ipmr_destroy_unres(c); //如果发现超时的缓存项 调ipmr_destroy_unres将其删除释放
	}

	if (atomic_read(&cache_resolve_queue_len)) //如果对临时组播转发缓存队列处理后 还存在临时组播转发缓存项 则需重新设置定时器超时时间
		mod_timer(&ipmr_expire_timer, jiffies + expires);

out:
	spin_unlock(&mfc_unres_lock);
}

/* Fill oifs list. It is called under write locked mrt_lock. */

static void ipmr_update_thresholds(struct mfc_cache *cache, unsigned char *ttls)
{
	int vifi;

	cache->mfc_un.res.minvif = MAXVIFS;
	cache->mfc_un.res.maxvif = 0;
	memset(cache->mfc_un.res.ttls, 255, MAXVIFS);

	for (vifi=0; vifi<maxvif; vifi++) {
		if (VIF_EXISTS(vifi) && ttls[vifi] && ttls[vifi] < 255) {
			cache->mfc_un.res.ttls[vifi] = ttls[vifi];
			if (cache->mfc_un.res.minvif > vifi)
				cache->mfc_un.res.minvif = vifi;
			if (cache->mfc_un.res.maxvif <= vifi)
				cache->mfc_un.res.maxvif = vifi + 1;
		}
	}
}

static int vif_add(struct vifctl *vifc, int mrtsock)
{
	int vifi = vifc->vifc_vifi;
	struct vif_device *v = &vif_table[vifi];
	struct net_device *dev;
	struct in_device *in_dev;

	/* Is vif busy ? */
	if (VIF_EXISTS(vifi)) //获取待设置的虚拟接口 &检查该虚拟接口的网卡是否可用
		return -EADDRINUSE;

	switch (vifc->vifc_flags) {
#ifdef CONFIG_IP_PIMSM //如果编译支持ip_pimsm选项 &添加虚拟接口标志为viff_register则调ipmr_reg_vif创建用于接收pim协议报文的网卡
	case VIFF_REGISTER:
		/*
		 * Special Purpose VIF in PIM
		 * All the packets will be sent to the daemon
		 */
		if (reg_vif_num >= 0)
			return -EADDRINUSE;
		dev = ipmr_reg_vif();
		if (!dev)
			return -ENOBUFS;
		break;
#endif
	case VIFF_TUNNEL:	//当添加虚拟接口标志为 viff_tunnel时 调ipmr_new_tunnel根据配置信息来配置&获取隧道网络设备
		dev = ipmr_new_tunnel(vifc);
		if (!dev)
			return -ENOBUFS;
		break;
	case 0: //当添加虚拟接口标志为0时 调ip_dev_find根据本地地址获取对应的网卡 并增加该设备的引用计数
		dev = ip_dev_find(vifc->vifc_lcl_addr.s_addr);
		if (!dev)
			return -EADDRNOTAVAIL;
		dev_put(dev);
		break;
	default:
		return -EINVAL;
	}

	if ((in_dev = __in_dev_get_rtnl(dev)) == NULL) //获取网卡的ip配置块失败
		return -EADDRNOTAVAIL;
	in_dev->cnf.mc_forwarding++;
	dev_set_allmulti(dev, +1); //更新网卡上组播转发标志
	ip_rt_multicast_event(in_dev); //更新网卡allmuti标志 当值>0时 在该网卡上启用接收组播报文功能 接着刷新路由

	/*
	 *	Fill in the VIF structures
	 */
	v->rate_limit=vifc->vifc_rate_limit; //最后将配置信息填充到虚拟接口数据结构中 &更新目前虚拟接口索引的最大值maxvif
	v->local=vifc->vifc_lcl_addr.s_addr;
	v->remote=vifc->vifc_rmt_addr.s_addr;
	v->flags=vifc->vifc_flags;
	if (!mrtsock)
		v->flags |= VIFF_STATIC;
	v->threshold=vifc->vifc_threshold;
	v->bytes_in = 0;
	v->bytes_out = 0;
	v->pkt_in = 0;
	v->pkt_out = 0;
	v->link = dev->ifindex;
	if (v->flags&(VIFF_TUNNEL|VIFF_REGISTER))
		v->link = dev->iflink;

	/* And finish update writing critical data */
	write_lock_bh(&mrt_lock);
	dev_hold(dev);
	v->dev=dev;
#ifdef CONFIG_IP_PIMSM
	if (v->flags&VIFF_REGISTER)
		reg_vif_num = vifi;
#endif
	if (vifi+1 > maxvif)
		maxvif = vifi+1;
	write_unlock_bh(&mrt_lock);
	return 0;
}

static struct mfc_cache *ipmr_cache_find(__be32 origin, __be32 mcastgrp)
{
	int line=MFC_HASH(mcastgrp,origin);
	struct mfc_cache *c;

	for (c=mfc_cache_array[line]; c; c = c->next) {
		if (c->mfc_origin==origin && c->mfc_mcastgrp==mcastgrp)
			break;
	}
	return c;
}

/*
 *	Allocate a multicast cache entry
 */
static struct mfc_cache *ipmr_cache_alloc(void)
{
	struct mfc_cache *c=kmem_cache_alloc(mrt_cachep, GFP_KERNEL);
	if(c==NULL)
		return NULL;
	memset(c, 0, sizeof(*c));
	c->mfc_un.res.minvif = MAXVIFS;
	return c;
}

static struct mfc_cache *ipmr_cache_alloc_unres(void) //用于在mrt_cachep缓存池中分配一个临时组播转发缓存项&初始化其定时器
{
	struct mfc_cache *c=kmem_cache_alloc(mrt_cachep, GFP_ATOMIC);
	if(c==NULL)
		return NULL;
	memset(c, 0, sizeof(*c));
	skb_queue_head_init(&c->mfc_un.unres.unresolved);
	c->mfc_un.unres.expires = jiffies + 10*HZ;
	return c;
}

/*
 *	A cache entry has gone into a resolved state from queued
 */
 
static void ipmr_cache_resolve(struct mfc_cache *uc, struct mfc_cache *c)
{
	struct sk_buff *skb;
	struct nlmsgerr *e;

	/*
	 *	Play the pending entries through our router
	 */

	while((skb=__skb_dequeue(&uc->mfc_un.unres.unresolved))) {
		if (skb->nh.iph->version == 0) {
			struct nlmsghdr *nlh = (struct nlmsghdr *)skb_pull(skb, sizeof(struct iphdr));

			if (ipmr_fill_mroute(skb, c, NLMSG_DATA(nlh)) > 0) {
				nlh->nlmsg_len = skb->tail - (u8*)nlh;
			} else {
				nlh->nlmsg_type = NLMSG_ERROR;
				nlh->nlmsg_len = NLMSG_LENGTH(sizeof(struct nlmsgerr));
				skb_trim(skb, nlh->nlmsg_len);
				e = NLMSG_DATA(nlh);
				e->error = -EMSGSIZE;
				memset(&e->msg, 0, sizeof(e->msg));
			}

			rtnl_unicast(skb, NETLINK_CB(skb).pid);
		} else
			ip_mr_forward(skb, c, 0);
	}
}

/*
 *	Bounce a cache query up to mrouted. We could use netlink for this but mrouted
 *	expects the following bizarre scheme.
 *
 *	Called under mrt_lock.
 */
 
static int ipmr_cache_report(struct sk_buff *pkt, vifi_t vifi, int assert)
{
	struct sk_buff *skb;
	int ihl = pkt->nh.iph->ihl<<2;
	struct igmphdr *igmp;
	struct igmpmsg *msg;
	int ret;

#ifdef CONFIG_IP_PIMSM
	if (assert == IGMPMSG_WHOLEPKT)
		skb = skb_realloc_headroom(pkt, sizeof(struct iphdr));
	else
#endif
		skb = alloc_skb(128, GFP_ATOMIC);

	if(!skb)
		return -ENOBUFS;

#ifdef CONFIG_IP_PIMSM
	if (assert == IGMPMSG_WHOLEPKT) {
		/* Ugly, but we have no choice with this interface.
		   Duplicate old header, fix ihl, length etc.
		   And all this only to mangle msg->im_msgtype and
		   to set msg->im_mbz to "mbz" :-)
		 */
		msg = (struct igmpmsg*)skb_push(skb, sizeof(struct iphdr));
		skb->nh.raw = skb->h.raw = (u8*)msg;
		memcpy(msg, pkt->nh.raw, sizeof(struct iphdr));
		msg->im_msgtype = IGMPMSG_WHOLEPKT;
		msg->im_mbz = 0;
 		msg->im_vif = reg_vif_num;
		skb->nh.iph->ihl = sizeof(struct iphdr) >> 2;
		skb->nh.iph->tot_len = htons(ntohs(pkt->nh.iph->tot_len) + sizeof(struct iphdr));
	} else 
#endif
	{	
		
	/*
	 *	Copy the IP header
	 */

	skb->nh.iph = (struct iphdr *)skb_put(skb, ihl);
	memcpy(skb->data,pkt->data,ihl);
	skb->nh.iph->protocol = 0;			/* Flag to the kernel this is a route add */
	msg = (struct igmpmsg*)skb->nh.iph;
	msg->im_vif = vifi;
	skb->dst = dst_clone(pkt->dst);

	/*
	 *	Add our header
	 */

	igmp=(struct igmphdr *)skb_put(skb,sizeof(struct igmphdr));
	igmp->type	=
	msg->im_msgtype = assert;
	igmp->code 	=	0;
	skb->nh.iph->tot_len=htons(skb->len);			/* Fix the length */
	skb->h.raw = skb->nh.raw;
        }

	if (mroute_socket == NULL) {
		kfree_skb(skb);
		return -EINVAL;
	}

	/*
	 *	Deliver to mrouted
	 */
	if ((ret=sock_queue_rcv_skb(mroute_socket,skb))<0) {
		if (net_ratelimit())
			printk(KERN_WARNING "mroute: pending queue full, dropping entries.\n");
		kfree_skb(skb);
	}

	return ret;
}

/*
 *	Queue a packet for resolution. It gets locked cache entry!
 */
 
static int
ipmr_cache_unresolved(vifi_t vifi, struct sk_buff *skb) //1创建临时组播转发缓存项 2向组播路由守护进程发送IGMPMSG_NOCACHE报告 3启动定时器 4缓存该组播报文到对应临时组播转发缓存项中
{
	int err;
	struct mfc_cache *c;

	spin_lock_bh(&mfc_unres_lock);
	for (c=mfc_unres_queue; c; c=c->next) { //根据组播报文的源地址和组播地址 在临时组播转发缓存队列mfc_unres_queue中查找是否已存在对应的临时组播转发缓存项 存在则只需将该组播报文缓存到找到的临时组播转发缓存项中
		if (c->mfc_mcastgrp == skb->nh.iph->daddr &&
		    c->mfc_origin == skb->nh.iph->saddr)
			break;
	}

	if (c == NULL) { //如果找不到对应的临时组播转发缓存 则进行创建&复位定时器
		/*
		 *	Create a new entry if allowable
		 */

		if (atomic_read(&cache_resolve_queue_len)>=10 ||
		    (c=ipmr_cache_alloc_unres())==NULL) { //如果临时组播转发缓存队列长度已经到达上限值10 则不能再创建新的临时组播转发缓存 只能丢弃该组播报文 否则调用ipmr_cache_alloc_unres分配一条新的临时组播转发缓存
			spin_unlock_bh(&mfc_unres_lock);

			kfree_skb(skb);
			return -ENOBUFS;
		}

		/*
		 *	Fill in the new cache entry
		 */
		c->mfc_parent=-1; //初始化新分配的临时组播转发缓存 包括源地址 组播地址
		c->mfc_origin=skb->nh.iph->saddr;
		c->mfc_mcastgrp=skb->nh.iph->daddr;

		/*
		 *	Reflect first query at mrouted.
		 */
		if ((err = ipmr_cache_report(skb, vifi, IGMPMSG_NOCACHE))<0) { //向组播路由守护进程发送IGMPMGS_NOCACHE类型报告 通知组播路由守护进程来处理该未确定组播路由缓存
			/* If the report failed throw the cache entry 
			   out - Brad Parker
			 */
			spin_unlock_bh(&mfc_unres_lock);

			kmem_cache_free(mrt_cachep, c);
			kfree_skb(skb);
			return err;
		}

		atomic_inc(&cache_resolve_queue_len); //将新创建的临时组播转发缓存项添加到mfc_unres_queue队列中
		c->next = mfc_unres_queue;
		mfc_unres_queue = c;

		mod_timer(&ipmr_expire_timer, c->mfc_un.unres.expires); //重新复位定时器
	}

	/*
	 *	See if we can append the packet
	 */
	if (c->mfc_un.unres.unresolved.qlen>3) { //如果组播报文对应的临时组播转发缓存中 缓存组播报文数达上限值3 则只能丢弃该组播报文
		kfree_skb(skb);
		err = -ENOBUFS;
	} else {
		skb_queue_tail(&c->mfc_un.unres.unresolved,skb); //否则将该组播报文缓存到临时组播转发缓存项中
		err = 0;
	}

	spin_unlock_bh(&mfc_unres_lock);
	return err;
}

/*
 *	MFC cache manipulation by user space mroute daemon
 */

static int ipmr_mfc_delete(struct mfcctl *mfc)
{
	int line;
	struct mfc_cache *c, **cp;

	line=MFC_HASH(mfc->mfcc_mcastgrp.s_addr, mfc->mfcc_origin.s_addr);

	for (cp=&mfc_cache_array[line]; (c=*cp) != NULL; cp = &c->next) {
		if (c->mfc_origin == mfc->mfcc_origin.s_addr &&
		    c->mfc_mcastgrp == mfc->mfcc_mcastgrp.s_addr) {
			write_lock_bh(&mrt_lock);
			*cp = c->next;
			write_unlock_bh(&mrt_lock);

			kmem_cache_free(mrt_cachep, c);
			return 0;
		}
	}
	return -ENOENT;
}

static int ipmr_mfc_add(struct mfcctl *mfc, int mrtsock)
{
	int line;
	struct mfc_cache *uc, *c, **cp;

	line=MFC_HASH(mfc->mfcc_mcastgrp.s_addr, mfc->mfcc_origin.s_addr);

	for (cp=&mfc_cache_array[line]; (c=*cp) != NULL; cp = &c->next) {
		if (c->mfc_origin == mfc->mfcc_origin.s_addr &&
		    c->mfc_mcastgrp == mfc->mfcc_mcastgrp.s_addr)
			break;
	}

	if (c != NULL) {
		write_lock_bh(&mrt_lock);
		c->mfc_parent = mfc->mfcc_parent;
		ipmr_update_thresholds(c, mfc->mfcc_ttls);
		if (!mrtsock)
			c->mfc_flags |= MFC_STATIC;
		write_unlock_bh(&mrt_lock);
		return 0;
	}

	if(!MULTICAST(mfc->mfcc_mcastgrp.s_addr))
		return -EINVAL;

	c=ipmr_cache_alloc();
	if (c==NULL)
		return -ENOMEM;

	c->mfc_origin=mfc->mfcc_origin.s_addr;
	c->mfc_mcastgrp=mfc->mfcc_mcastgrp.s_addr;
	c->mfc_parent=mfc->mfcc_parent;
	ipmr_update_thresholds(c, mfc->mfcc_ttls);
	if (!mrtsock)
		c->mfc_flags |= MFC_STATIC;

	write_lock_bh(&mrt_lock);
	c->next = mfc_cache_array[line];
	mfc_cache_array[line] = c;
	write_unlock_bh(&mrt_lock);

	/*
	 *	Check to see if we resolved a queued list. If so we
	 *	need to send on the frames and tidy up.
	 */
	spin_lock_bh(&mfc_unres_lock);
	for (cp = &mfc_unres_queue; (uc=*cp) != NULL;
	     cp = &uc->next) {
		if (uc->mfc_origin == c->mfc_origin &&
		    uc->mfc_mcastgrp == c->mfc_mcastgrp) {
			*cp = uc->next;
			if (atomic_dec_and_test(&cache_resolve_queue_len))
				del_timer(&ipmr_expire_timer);
			break;
		}
	}
	spin_unlock_bh(&mfc_unres_lock);

	if (uc) {
		ipmr_cache_resolve(uc, c);
		kmem_cache_free(mrt_cachep, uc);
	}
	return 0;
}

/*
 *	Close the multicast socket, and clear the vif tables etc
 */
 
static void mroute_clean_tables(struct sock *sk)
{
	int i;
		
	/*
	 *	Shut down all active vif entries
	 */
	for(i=0; i<maxvif; i++) {
		if (!(vif_table[i].flags&VIFF_STATIC))
			vif_delete(i);
	}

	/*
	 *	Wipe the cache
	 */
	for (i=0;i<MFC_LINES;i++) {
		struct mfc_cache *c, **cp;

		cp = &mfc_cache_array[i];
		while ((c = *cp) != NULL) {
			if (c->mfc_flags&MFC_STATIC) {
				cp = &c->next;
				continue;
			}
			write_lock_bh(&mrt_lock);
			*cp = c->next;
			write_unlock_bh(&mrt_lock);

			kmem_cache_free(mrt_cachep, c);
		}
	}

	if (atomic_read(&cache_resolve_queue_len) != 0) {
		struct mfc_cache *c;

		spin_lock_bh(&mfc_unres_lock);
		while (mfc_unres_queue != NULL) {
			c = mfc_unres_queue;
			mfc_unres_queue = c->next;
			spin_unlock_bh(&mfc_unres_lock);

			ipmr_destroy_unres(c);

			spin_lock_bh(&mfc_unres_lock);
		}
		spin_unlock_bh(&mfc_unres_lock);
	}
}

static void mrtsock_destruct(struct sock *sk)
{
	rtnl_lock();
	if (sk == mroute_socket) {
		ipv4_devconf.mc_forwarding--;

		write_lock_bh(&mrt_lock);
		mroute_socket=NULL;
		write_unlock_bh(&mrt_lock);

		mroute_clean_tables(sk);
	}
	rtnl_unlock();
}

/*
 *	Socket options and virtual interface manipulation. The whole
 *	virtual interface system is a complete heap, but unfortunately
 *	that's how BSD mrouted happens to think. Maybe one day with a proper
 *	MOSPF/PIM router set up we can clean this up.
 */
 
int ip_mroute_setsockopt(struct sock *sk,int optname,char __user *optval,int optlen)
{
	int ret;
	struct vifctl vif;
	struct mfcctl mfc;
	
	if(optname!=MRT_INIT)
	{
		if(sk!=mroute_socket && !capable(CAP_NET_ADMIN))
			return -EACCES;
	}

	switch(optname)
	{
		case MRT_INIT:
			if (sk->sk_type != SOCK_RAW ||
			    inet_sk(sk)->num != IPPROTO_IGMP)
				return -EOPNOTSUPP;
			if(optlen!=sizeof(int))
				return -ENOPROTOOPT;

			rtnl_lock();
			if (mroute_socket) {
				rtnl_unlock();
				return -EADDRINUSE;
			}

			ret = ip_ra_control(sk, 1, mrtsock_destruct);
			if (ret == 0) {
				write_lock_bh(&mrt_lock);
				mroute_socket=sk;
				write_unlock_bh(&mrt_lock);

				ipv4_devconf.mc_forwarding++;
			}
			rtnl_unlock();
			return ret;
		case MRT_DONE:
			if (sk!=mroute_socket)
				return -EACCES;
			return ip_ra_control(sk, 0, NULL);
		case MRT_ADD_VIF:
		case MRT_DEL_VIF:
			if(optlen!=sizeof(vif))
				return -EINVAL;
			if (copy_from_user(&vif,optval,sizeof(vif)))
				return -EFAULT; 
			if(vif.vifc_vifi >= MAXVIFS)
				return -ENFILE;
			rtnl_lock();
			if (optname==MRT_ADD_VIF) {
				ret = vif_add(&vif, sk==mroute_socket);
			} else {
				ret = vif_delete(vif.vifc_vifi);
			}
			rtnl_unlock();
			return ret;

		/*
		 *	Manipulate the forwarding caches. These live
		 *	in a sort of kernel/user symbiosis.
		 */
		case MRT_ADD_MFC:
		case MRT_DEL_MFC:
			if(optlen!=sizeof(mfc))
				return -EINVAL;
			if (copy_from_user(&mfc,optval, sizeof(mfc)))
				return -EFAULT;
			rtnl_lock();
			if (optname==MRT_DEL_MFC)
				ret = ipmr_mfc_delete(&mfc);
			else
				ret = ipmr_mfc_add(&mfc, sk==mroute_socket);
			rtnl_unlock();
			return ret;
		/*
		 *	Control PIM assert.
		 */
		case MRT_ASSERT:
		{
			int v;
			if(get_user(v,(int __user *)optval))
				return -EFAULT;
			mroute_do_assert=(v)?1:0;
			return 0;
		}
#ifdef CONFIG_IP_PIMSM
		case MRT_PIM:
		{
			int v, ret;
			if(get_user(v,(int __user *)optval))
				return -EFAULT;
			v = (v)?1:0;
			rtnl_lock();
			ret = 0;
			if (v != mroute_do_pim) {
				mroute_do_pim = v;
				mroute_do_assert = v;
#ifdef CONFIG_IP_PIMSM_V2
				if (mroute_do_pim)
					ret = inet_add_protocol(&pim_protocol,
								IPPROTO_PIM);
				else
					ret = inet_del_protocol(&pim_protocol,
								IPPROTO_PIM);
				if (ret < 0)
					ret = -EAGAIN;
#endif
			}
			rtnl_unlock();
			return ret;
		}
#endif
		/*
		 *	Spurious command, or MRT_VERSION which you cannot
		 *	set.
		 */
		default:
			return -ENOPROTOOPT;
	}
}

/*
 *	Getsock opt support for the multicast routing system.
 */
 
int ip_mroute_getsockopt(struct sock *sk,int optname,char __user *optval,int __user *optlen)
{
	int olr;
	int val;

	if(optname!=MRT_VERSION && 
#ifdef CONFIG_IP_PIMSM
	   optname!=MRT_PIM &&
#endif
	   optname!=MRT_ASSERT)
		return -ENOPROTOOPT;

	if (get_user(olr, optlen))
		return -EFAULT;

	olr = min_t(unsigned int, olr, sizeof(int));
	if (olr < 0)
		return -EINVAL;
		
	if(put_user(olr,optlen))
		return -EFAULT;
	if(optname==MRT_VERSION)
		val=0x0305;
#ifdef CONFIG_IP_PIMSM
	else if(optname==MRT_PIM)
		val=mroute_do_pim;
#endif
	else
		val=mroute_do_assert;
	if(copy_to_user(optval,&val,olr))
		return -EFAULT;
	return 0;
}

/*
 *	The IP multicast ioctl support routines.
 */
 
int ipmr_ioctl(struct sock *sk, int cmd, void __user *arg)
{
	struct sioc_sg_req sr;
	struct sioc_vif_req vr;
	struct vif_device *vif;
	struct mfc_cache *c;
	
	switch(cmd)
	{
		case SIOCGETVIFCNT:
			if (copy_from_user(&vr,arg,sizeof(vr)))
				return -EFAULT; 
			if(vr.vifi>=maxvif)
				return -EINVAL;
			read_lock(&mrt_lock);
			vif=&vif_table[vr.vifi];
			if(VIF_EXISTS(vr.vifi))	{
				vr.icount=vif->pkt_in;
				vr.ocount=vif->pkt_out;
				vr.ibytes=vif->bytes_in;
				vr.obytes=vif->bytes_out;
				read_unlock(&mrt_lock);

				if (copy_to_user(arg,&vr,sizeof(vr)))
					return -EFAULT;
				return 0;
			}
			read_unlock(&mrt_lock);
			return -EADDRNOTAVAIL;
		case SIOCGETSGCNT:
			if (copy_from_user(&sr,arg,sizeof(sr)))
				return -EFAULT;

			read_lock(&mrt_lock);
			c = ipmr_cache_find(sr.src.s_addr, sr.grp.s_addr);
			if (c) {
				sr.pktcnt = c->mfc_un.res.pkt;
				sr.bytecnt = c->mfc_un.res.bytes;
				sr.wrong_if = c->mfc_un.res.wrong_if;
				read_unlock(&mrt_lock);

				if (copy_to_user(arg,&sr,sizeof(sr)))
					return -EFAULT;
				return 0;
			}
			read_unlock(&mrt_lock);
			return -EADDRNOTAVAIL;
		default:
			return -ENOIOCTLCMD;
	}
}


static int ipmr_device_event(struct notifier_block *this, unsigned long event, void *ptr)
{
	struct vif_device *v;
	int ct;
	if (event != NETDEV_UNREGISTER)
		return NOTIFY_DONE;
	v=&vif_table[0];
	for(ct=0;ct<maxvif;ct++,v++) {
		if (v->dev==ptr)
			vif_delete(ct);
	}
	return NOTIFY_DONE;
}


static struct notifier_block ip_mr_notifier={
	.notifier_call = ipmr_device_event,
};

/*
 * 	Encapsulate a packet by attaching a valid IPIP header to it.
 *	This avoids tunnel drivers and other mess and gives us the speed so
 *	important for multicast video.
 */
 
static void ip_encap(struct sk_buff *skb, __be32 saddr, __be32 daddr)
{
	struct iphdr *iph = (struct iphdr *)skb_push(skb,sizeof(struct iphdr));

	iph->version	= 	4;
	iph->tos	=	skb->nh.iph->tos;
	iph->ttl	=	skb->nh.iph->ttl;
	iph->frag_off	=	0;
	iph->daddr	=	daddr;
	iph->saddr	=	saddr;
	iph->protocol	=	IPPROTO_IPIP;
	iph->ihl	=	5;
	iph->tot_len	=	htons(skb->len);
	ip_select_ident(iph, skb->dst, NULL);
	ip_send_check(iph);

	skb->h.ipiph = skb->nh.iph;
	skb->nh.iph = iph;
	memset(&(IPCB(skb)->opt), 0, sizeof(IPCB(skb)->opt));
	nf_reset(skb);
}

static inline int ipmr_forward_finish(struct sk_buff *skb)
{
	struct ip_options * opt	= &(IPCB(skb)->opt);

	IP_INC_STATS_BH(IPSTATS_MIB_OUTFORWDATAGRAMS);

	if (unlikely(opt->optlen))
		ip_forward_options(skb);

	return dst_output(skb);
}

/*
 *	Processing handlers for ipmr_forward
 */

static void ipmr_queue_xmit(struct sk_buff *skb, struct mfc_cache *c, int vifi) //用来转发组播报文 在ip_mr_forward中调
{
	struct iphdr *iph = skb->nh.iph; //检测输出虚拟接口对应的网卡是否有效
	struct vif_device *vif = &vif_table[vifi];
	struct net_device *dev;
	struct rtable *rt;
	int    encap = 0;

	if (vif->dev == NULL)
		goto out_free;

#ifdef CONFIG_IP_PIMSM
	if (vif->flags & VIFF_REGISTER) { //将IGMPMSG_WHOLEPKT类型的报告发送给路由守护进程
		vif->pkt_out++;
		vif->bytes_out+=skb->len;
		((struct net_device_stats*)netdev_priv(vif->dev))->tx_bytes += skb->len;
		((struct net_device_stats*)netdev_priv(vif->dev))->tx_packets++;
		ipmr_cache_report(skb, vifi, IGMPMSG_WHOLEPKT);
		kfree_skb(skb);
		return;
	}
#endif

	if (vif->flags&VIFF_TUNNEL) { //如果输出设备对应的虚拟接口是隧道类型 则根据隧道终点ip地址查找路由 否则 根据组播报文的目的地址查找路由 如果找不到路由则丢弃
		struct flowi fl = { .oif = vif->link,
				    .nl_u = { .ip4_u =
					      { .daddr = vif->remote,
						.saddr = vif->local,
						.tos = RT_TOS(iph->tos) } },
				    .proto = IPPROTO_IPIP };
		if (ip_route_output_key(&rt, &fl))
			goto out_free;
		encap = sizeof(struct iphdr);
	} else {
		struct flowi fl = { .oif = vif->link,
				    .nl_u = { .ip4_u =
					      { .daddr = iph->daddr,
						.tos = RT_TOS(iph->tos) } },
				    .proto = IPPROTO_IPIP };
		if (ip_route_output_key(&rt, &fl))
			goto out_free;
	}

	dev = rt->u.dst.dev; //获取组播报文输出的网卡

	if (skb->len+encap > dst_mtu(&rt->u.dst) && (ntohs(iph->frag_off) & IP_DF)) { //如果报文长度大于路径mtu 且报文设置不允许分片 则不能转发该组播报文 递减对已找到路由的引用 释放该报文
		/* Do not fragment multicasts. Alas, IPv4 does not
		   allow to send ICMP, so that packets will disappear
		   to blackhole.
		 */

		IP_INC_STATS_BH(IPSTATS_MIB_FRAGFAILS);
		ip_rt_put(rt);
		goto out_free;
	}

	encap += LL_RESERVED_SPACE(dev) + rt->u.dst.header_len; //检测转发的组播报文其skb的headroom部分是否有足够空间

	if (skb_cow(skb, encap)) {
 		ip_rt_put(rt);
		goto out_free;
	}

	vif->pkt_out++; //对组播报文进行转发
	vif->bytes_out+=skb->len; //更新从该虚拟接口输出的报文总字节数和报文总数

	dst_release(skb->dst); //用查询得到的输出路由缓存更新skb的目的路由缓存
	skb->dst = &rt->u.dst;
	iph = skb->nh.iph;
	ip_decrease_ttl(iph); //递减转发组播报文的ttl

	/* FIXME: forward and output firewalls used to be called here.
	 * What do we do with netfilter? -- RR */
	if (vif->flags & VIFF_TUNNEL) { //处理ipip隧道类型虚拟接口
		ip_encap(skb, vif->local, vif->remote);
		/* FIXME: extra output firewall step used to be here. --RR */
		((struct ip_tunnel *)netdev_priv(vif->dev))->stat.tx_packets++;
		((struct ip_tunnel *)netdev_priv(vif->dev))->stat.tx_bytes+=skb->len;
	}

	IPCB(skb)->flags |= IPSKB_FORWARDED; //设置ip控制块的ipskb_forwarded标志 标识该报文已转发

	/*
	 * RFC1584 teaches, that DVMRP/PIM router must deliver packets locally
	 * not only before forwarding, but after forwarding on all output
	 * interfaces. It is clear, if mrouter runs a multicasting
	 * program, it should receive packets not depending to what interface
	 * program is joined.
	 * If we will not make it, the program will have to join on all
	 * interfaces. On the other hand, multihoming host (or router, but
	 * not mrouter) cannot join to more than one interface - it will
	 * result in receiving multiple packets.
	 */
	NF_HOOK(PF_INET, NF_IP_FORWARD, skb, skb->dev, dev,  //通过netfilter的forward点 对报文进行过滤等规则检测后 调ipmr_forward_finish进行组播报文的输出处理
		ipmr_forward_finish);
	return;

out_free:
	kfree_skb(skb); //如果不能转发组播报文 跳转到这里释放报文
	return;
}

static int ipmr_find_vif(struct net_device *dev) //在输入或转发组播报文时调用
{
	int ct;
	for (ct=maxvif-1; ct>=0; ct--) {
		if (vif_table[ct].dev == dev)
			break;
	}
	return ct;
}

/* "local" means that we should preserve one skb (for local delivery) */

static int ip_mr_forward(struct sk_buff *skb, struct mfc_cache *cache, int local) //在处理输入的组播报文时 如果查找到组播转发缓存 则说明该组播报文需要转发 组播报文的转发有ip_mr_forward完成
{                                    //待转发的组播报文 允许该组播报进行转发的转发缓存 当local为非0时 表示该组播包转发后是否还需要发送到本地 因此需要复制一份组播报文进行转发
	int psend = -1;
	int vif, ct;

	vif = cache->mfc_parent;
	cache->mfc_un.res.pkt++;
	cache->mfc_un.res.bytes += skb->len; //更新该组播转发缓存转发的总字节数和总报文数 包括在找不到对应输入设备虚拟接口的情况下不会被转发的报文

	/*
	 * Wrong interface: drop packet and (maybe) send PIM assert.
	 */
	if (vif_table[vif].dev != skb->dev) { //处理找不到对应输入的虚拟接口的情况
		int true_vifi;

		if (((struct rtable*)skb->dst)->fl.iif == 0) { //在找不到该组播报文输入设备虚拟接口&输入网卡有异常情况下 不能转发报文
			/* It is our own packet, looped back.
			   Very complicated situation...

			   The best workaround until routing daemons will be
			   fixed is not to redistribute packet, if it was
			   send through wrong interface. It means, that
			   multicast applications WILL NOT work for
			   (S,G), which have default multicast route pointing
			   to wrong oif. In any case, it is not a good
			   idea to use multicasting applications on router.
			 */
			goto dont_forward;
		}

		cache->mfc_un.res.wrong_if++; //跟新转发过程失败计数
		true_vifi = ipmr_find_vif(skb->dev);

		if (true_vifi >= 0 && mroute_do_assert && //根据组播报文的输入网卡重新查找对应的虚拟接口 一旦查找成功 并且设置了需要发送路由警告 同时接受pim协议或转发缓存中对应网卡的ttl有效时 发送IGMPMSG_WRONGVIF类型的报告 用于在PIM-SM组播路由器之间选择最短路径或触发一个pim声明消息
		    /* pimsm uses asserts, when switching from RPT to SPT,
		       so that we cannot check that packet arrived on an oif.
		       It is bad, but otherwise we would need to move pretty
		       large chunk of pimd to kernel. Ough... --ANK
		     */
		    (mroute_do_pim || cache->mfc_un.res.ttls[true_vifi] < 255) &&
		    time_after(jiffies, 
			       cache->mfc_un.res.last_assert + MFC_ASSERT_THRESH)) {
			cache->mfc_un.res.last_assert = jiffies;
			ipmr_cache_report(skb, true_vifi, IGMPMSG_WRONGVIF);
		}
		goto dont_forward; //找不到转发缓存 不能转发组播报文
	}

	vif_table[vif].pkt_in++; //更新对应虚拟接口的输入组播报文总字节数和输入组播报文总数
	vif_table[vif].bytes_in+=skb->len;

	/*
	 *	Forward the frame
	 */
	for (ct = cache->mfc_un.res.maxvif-1; ct >= cache->mfc_un.res.minvif; ct--) { //向各个虚拟接口转发组播报文
		if (skb->nh.iph->ttl > cache->mfc_un.res.ttls[ct]) { //遍历组播转发缓存的ttls数组 比较组播报文的ttl与虚拟设备的ttl阈值 报文只能从阈值小于报文ttl的虚拟接口中输出
			if (psend != -1) {
				struct sk_buff *skb2 = skb_clone(skb, GFP_ATOMIC);
				if (skb2)
					ipmr_queue_xmit(skb2, cache, psend);
			}
			psend=ct;
		}
	}
	if (psend != -1) { //从最后一个符合条件的虚拟接口转发报文 如果报文需要发送到本地 则复制一个报文发送 否则直接发送
		if (local) {
			struct sk_buff *skb2 = skb_clone(skb, GFP_ATOMIC);
			if (skb2)
				ipmr_queue_xmit(skb2, cache, psend);
		} else {
			ipmr_queue_xmit(skb, cache, psend);
			return 0;
		}
	}

dont_forward: //在不能转发的情形下 如果也无需发送到本地 则释放该报文
	if (!local)
		kfree_skb(skb);
	return 0;
}


/*
 *	Multicast packets for forwarding arrive here
 */

int ip_mr_input(struct sk_buff *skb) //对于输入到本地或转发的组播报文 在经过netfilter处理后会调ip_rcv_finish正式进入输入处理 先调ip_route_input进行输入路由查询 若发现目的地址为组播地址
{                                     //就会安装组播地址的规则查找路由 查找到组播的输入路由后 组播报文接收 组播报文接收处理函数为ip_mr_input
	struct mfc_cache *cache;
	int local = ((struct rtable*)skb->dst)->rt_flags&RTCF_LOCAL; //检测处理不发往本地的特殊报文

	/* Packet is looped back after forward, it should not be
	   forwarded second time, but still can be delivered locally.
	 */
	if (IPCB(skb)->flags&IPSKB_FORWARDED) //通过报文目的的路由中rt_flags标志来获取该组播包能否是发往本地的标志
		goto dont_forward;                  //如果该组播包已经转发过 则跳过转发部分代码 由于组播回环在组播转发之后进行 因此组播转发后需要设置标志 以免在进行回环时 再次进行转发

	if (!local) {
		    if (IPCB(skb)->opt.router_alert) { //如果报文不是发送往本地的 则检测ip的路由警告选项 如果存在该选项 则说明不能转发这个报文 应该传递给那些设置了ip_router_alert套接字选项的用户进程处理
			    if (ip_call_ra_chain(skb))
				    return 0;
		    } else if (skb->nh.iph->protocol == IPPROTO_IGMP){ //igmp协议报文不能放置路由警告选项 也不能由路由器转发 因此需要由mroute_socket(mrouted进程) 套接字接收
			    /* IGMPv1 (and broken IGMPv2 implementations sort of
			       Cisco IOS <= 11.2(8)) do not put router alert
			       option to IGMP packets destined to routable
			       groups. It is very bad, because it means
			       that we can forward NO IGMP messages.
			     */
			    read_lock(&mrt_lock);
			    if (mroute_socket) {
				    nf_reset(skb);
				    raw_rcv(mroute_socket, skb);
				    read_unlock(&mrt_lock);
				    return 0;
			    }
			    read_unlock(&mrt_lock);
		    }
	}

	read_lock(&mrt_lock);
	cache = ipmr_cache_find(skb->nh.iph->saddr, skb->nh.iph->daddr); //根据组播报文的源地址和目的地址查找组播转发缓存

	/*
	 *	No usable cache entry
	 */
	if (cache==NULL) { //处理找不到组播转发缓存的情况
		int vif;

		if (local) { //在找不到组播转发缓存的情况下处理发往本地的报文 需复制一个报文
			struct sk_buff *skb2 = skb_clone(skb, GFP_ATOMIC);
			ip_local_deliver(skb);
			if (skb2 == NULL) {
				read_unlock(&mrt_lock);
				return -ENOBUFS;
			}
			skb = skb2;
		}

		vif = ipmr_find_vif(skb->dev); //虽然找不到组播转发缓存 但输入网卡创建了虚拟网卡 则先添加一个临时组播转发缓存 并把需要转发的报文缓存下来 同时通知mrouted进程 需要添加这样的一条组播转发缓存
		if (vif >= 0) {
			int err = ipmr_cache_unresolved(vif, skb);
			read_unlock(&mrt_lock);

			return err;
		}
		read_unlock(&mrt_lock); //如果既找不到组播转发缓存 输入网卡也没有创建虚拟网卡 则说明该组播报并没有加入某个组 或者该组播包无效 则释放
		kfree_skb(skb);
		return -ENODEV;
	}

	ip_mr_forward(skb, cache, local); //组播报的转发 //找到了该组播报的组播转发缓存后 即可调ip_mr_forward转发该组播包

	read_unlock(&mrt_lock);

	if (local)
		return ip_local_deliver(skb); //如果该组播报是发送到本地的 则还需ip_local_deliver处理

	return 0;

dont_forward:
	if (local)
		return ip_local_deliver(skb);
	kfree_skb(skb);
	return 0;
}

#ifdef CONFIG_IP_PIMSM_V1
/*
 * Handle IGMP messages of PIMv1
 */

int pim_rcv_v1(struct sk_buff * skb)
{
	struct igmphdr *pim;
	struct iphdr   *encap;
	struct net_device  *reg_dev = NULL;

	if (!pskb_may_pull(skb, sizeof(*pim) + sizeof(*encap))) 
		goto drop;

	pim = (struct igmphdr*)skb->h.raw;

        if (!mroute_do_pim ||
	    skb->len < sizeof(*pim) + sizeof(*encap) ||
	    pim->group != PIM_V1_VERSION || pim->code != PIM_V1_REGISTER) 
		goto drop;

	encap = (struct iphdr*)(skb->h.raw + sizeof(struct igmphdr));
	/*
	   Check that:
	   a. packet is really destinted to a multicast group
	   b. packet is not a NULL-REGISTER
	   c. packet is not truncated
	 */
	if (!MULTICAST(encap->daddr) ||
	    encap->tot_len == 0 ||
	    ntohs(encap->tot_len) + sizeof(*pim) > skb->len) 
		goto drop;

	read_lock(&mrt_lock);
	if (reg_vif_num >= 0)
		reg_dev = vif_table[reg_vif_num].dev;
	if (reg_dev)
		dev_hold(reg_dev);
	read_unlock(&mrt_lock);

	if (reg_dev == NULL) 
		goto drop;

	skb->mac.raw = skb->nh.raw;
	skb_pull(skb, (u8*)encap - skb->data);
	skb->nh.iph = (struct iphdr *)skb->data;
	skb->dev = reg_dev;
	skb->protocol = htons(ETH_P_IP);
	skb->ip_summed = 0;
	skb->pkt_type = PACKET_HOST;
	dst_release(skb->dst);
	skb->dst = NULL;
	((struct net_device_stats*)netdev_priv(reg_dev))->rx_bytes += skb->len;
	((struct net_device_stats*)netdev_priv(reg_dev))->rx_packets++;
	nf_reset(skb);
	netif_rx(skb);
	dev_put(reg_dev);
	return 0;
 drop:
	kfree_skb(skb);
	return 0;
}
#endif

#ifdef CONFIG_IP_PIMSM_V2
static int pim_rcv(struct sk_buff * skb)
{
	struct pimreghdr *pim;
	struct iphdr   *encap;
	struct net_device  *reg_dev = NULL;

	if (!pskb_may_pull(skb, sizeof(*pim) + sizeof(*encap))) 
		goto drop;

	pim = (struct pimreghdr*)skb->h.raw;
        if (pim->type != ((PIM_VERSION<<4)|(PIM_REGISTER)) ||
	    (pim->flags&PIM_NULL_REGISTER) ||
	    (ip_compute_csum((void *)pim, sizeof(*pim)) != 0 && 
	     csum_fold(skb_checksum(skb, 0, skb->len, 0))))
		goto drop;

	/* check if the inner packet is destined to mcast group */
	encap = (struct iphdr*)(skb->h.raw + sizeof(struct pimreghdr));
	if (!MULTICAST(encap->daddr) ||
	    encap->tot_len == 0 ||
	    ntohs(encap->tot_len) + sizeof(*pim) > skb->len) 
		goto drop;

	read_lock(&mrt_lock);
	if (reg_vif_num >= 0)
		reg_dev = vif_table[reg_vif_num].dev;
	if (reg_dev)
		dev_hold(reg_dev);
	read_unlock(&mrt_lock);

	if (reg_dev == NULL) 
		goto drop;

	skb->mac.raw = skb->nh.raw;
	skb_pull(skb, (u8*)encap - skb->data);
	skb->nh.iph = (struct iphdr *)skb->data;
	skb->dev = reg_dev;
	skb->protocol = htons(ETH_P_IP);
	skb->ip_summed = 0;
	skb->pkt_type = PACKET_HOST;
	dst_release(skb->dst);
	((struct net_device_stats*)netdev_priv(reg_dev))->rx_bytes += skb->len;
	((struct net_device_stats*)netdev_priv(reg_dev))->rx_packets++;
	skb->dst = NULL;
	nf_reset(skb);
	netif_rx(skb);
	dev_put(reg_dev);
	return 0;
 drop:
	kfree_skb(skb);
	return 0;
}
#endif

static int
ipmr_fill_mroute(struct sk_buff *skb, struct mfc_cache *c, struct rtmsg *rtm)
{
	int ct;
	struct rtnexthop *nhp;
	struct net_device *dev = vif_table[c->mfc_parent].dev;
	u8 *b = skb->tail;
	struct rtattr *mp_head;

	if (dev)
		RTA_PUT(skb, RTA_IIF, 4, &dev->ifindex);

	mp_head = (struct rtattr*)skb_put(skb, RTA_LENGTH(0));

	for (ct = c->mfc_un.res.minvif; ct < c->mfc_un.res.maxvif; ct++) {
		if (c->mfc_un.res.ttls[ct] < 255) {
			if (skb_tailroom(skb) < RTA_ALIGN(RTA_ALIGN(sizeof(*nhp)) + 4))
				goto rtattr_failure;
			nhp = (struct rtnexthop*)skb_put(skb, RTA_ALIGN(sizeof(*nhp)));
			nhp->rtnh_flags = 0;
			nhp->rtnh_hops = c->mfc_un.res.ttls[ct];
			nhp->rtnh_ifindex = vif_table[ct].dev->ifindex;
			nhp->rtnh_len = sizeof(*nhp);
		}
	}
	mp_head->rta_type = RTA_MULTIPATH;
	mp_head->rta_len = skb->tail - (u8*)mp_head;
	rtm->rtm_type = RTN_MULTICAST;
	return 1;

rtattr_failure:
	skb_trim(skb, b - skb->data);
	return -EMSGSIZE;
}

int ipmr_get_route(struct sk_buff *skb, struct rtmsg *rtm, int nowait)
{
	int err;
	struct mfc_cache *cache;
	struct rtable *rt = (struct rtable*)skb->dst;

	read_lock(&mrt_lock);
	cache = ipmr_cache_find(rt->rt_src, rt->rt_dst);

	if (cache==NULL) {
		struct sk_buff *skb2;
		struct net_device *dev;
		int vif;

		if (nowait) {
			read_unlock(&mrt_lock);
			return -EAGAIN;
		}

		dev = skb->dev;
		if (dev == NULL || (vif = ipmr_find_vif(dev)) < 0) {
			read_unlock(&mrt_lock);
			return -ENODEV;
		}
		skb2 = skb_clone(skb, GFP_ATOMIC);
		if (!skb2) {
			read_unlock(&mrt_lock);
			return -ENOMEM;
		}

		skb2->nh.raw = skb_push(skb2, sizeof(struct iphdr));
		skb2->nh.iph->ihl = sizeof(struct iphdr)>>2;
		skb2->nh.iph->saddr = rt->rt_src;
		skb2->nh.iph->daddr = rt->rt_dst;
		skb2->nh.iph->version = 0;
		err = ipmr_cache_unresolved(vif, skb2);
		read_unlock(&mrt_lock);
		return err;
	}

	if (!nowait && (rtm->rtm_flags&RTM_F_NOTIFY))
		cache->mfc_flags |= MFC_NOTIFY;
	err = ipmr_fill_mroute(skb, cache, rtm);
	read_unlock(&mrt_lock);
	return err;
}

#ifdef CONFIG_PROC_FS	
/*
 *	The /proc interfaces to multicast routing /proc/ip_mr_cache /proc/ip_mr_vif
 */
struct ipmr_vif_iter {
	int ct;
};

static struct vif_device *ipmr_vif_seq_idx(struct ipmr_vif_iter *iter,
					   loff_t pos)
{
	for (iter->ct = 0; iter->ct < maxvif; ++iter->ct) {
		if(!VIF_EXISTS(iter->ct))
			continue;
		if (pos-- == 0) 
			return &vif_table[iter->ct];
	}
	return NULL;
}

static void *ipmr_vif_seq_start(struct seq_file *seq, loff_t *pos)
{
	read_lock(&mrt_lock);
	return *pos ? ipmr_vif_seq_idx(seq->private, *pos - 1) 
		: SEQ_START_TOKEN;
}

static void *ipmr_vif_seq_next(struct seq_file *seq, void *v, loff_t *pos)
{
	struct ipmr_vif_iter *iter = seq->private;

	++*pos;
	if (v == SEQ_START_TOKEN)
		return ipmr_vif_seq_idx(iter, 0);
	
	while (++iter->ct < maxvif) {
		if(!VIF_EXISTS(iter->ct))
			continue;
		return &vif_table[iter->ct];
	}
	return NULL;
}

static void ipmr_vif_seq_stop(struct seq_file *seq, void *v)
{
	read_unlock(&mrt_lock);
}

static int ipmr_vif_seq_show(struct seq_file *seq, void *v)
{
	if (v == SEQ_START_TOKEN) {
		seq_puts(seq, 
			 "Interface      BytesIn  PktsIn  BytesOut PktsOut Flags Local    Remote\n");
	} else {
		const struct vif_device *vif = v;
		const char *name =  vif->dev ? vif->dev->name : "none";

		seq_printf(seq,
			   "%2Zd %-10s %8ld %7ld  %8ld %7ld %05X %08X %08X\n",
			   vif - vif_table,
			   name, vif->bytes_in, vif->pkt_in, 
			   vif->bytes_out, vif->pkt_out,
			   vif->flags, vif->local, vif->remote);
	}
	return 0;
}

static struct seq_operations ipmr_vif_seq_ops = {
	.start = ipmr_vif_seq_start,
	.next  = ipmr_vif_seq_next,
	.stop  = ipmr_vif_seq_stop,
	.show  = ipmr_vif_seq_show,
};

static int ipmr_vif_open(struct inode *inode, struct file *file)
{
	struct seq_file *seq;
	int rc = -ENOMEM;
	struct ipmr_vif_iter *s = kmalloc(sizeof(*s), GFP_KERNEL);
       
	if (!s)
		goto out;

	rc = seq_open(file, &ipmr_vif_seq_ops);
	if (rc)
		goto out_kfree;

	s->ct = 0;
	seq = file->private_data;
	seq->private = s;
out:
	return rc;
out_kfree:
	kfree(s);
	goto out;

}

static struct file_operations ipmr_vif_fops = {
	.owner	 = THIS_MODULE,
	.open    = ipmr_vif_open,
	.read    = seq_read,
	.llseek  = seq_lseek,
	.release = seq_release_private,
};

struct ipmr_mfc_iter {
	struct mfc_cache **cache;
	int ct;
};


static struct mfc_cache *ipmr_mfc_seq_idx(struct ipmr_mfc_iter *it, loff_t pos)
{
	struct mfc_cache *mfc;

	it->cache = mfc_cache_array;
	read_lock(&mrt_lock);
	for (it->ct = 0; it->ct < MFC_LINES; it->ct++) 
		for(mfc = mfc_cache_array[it->ct]; mfc; mfc = mfc->next) 
			if (pos-- == 0) 
				return mfc;
	read_unlock(&mrt_lock);

	it->cache = &mfc_unres_queue;
	spin_lock_bh(&mfc_unres_lock);
	for(mfc = mfc_unres_queue; mfc; mfc = mfc->next) 
		if (pos-- == 0)
			return mfc;
	spin_unlock_bh(&mfc_unres_lock);

	it->cache = NULL;
	return NULL;
}


static void *ipmr_mfc_seq_start(struct seq_file *seq, loff_t *pos)
{
	struct ipmr_mfc_iter *it = seq->private;
	it->cache = NULL;
	it->ct = 0;
	return *pos ? ipmr_mfc_seq_idx(seq->private, *pos - 1) 
		: SEQ_START_TOKEN;
}

static void *ipmr_mfc_seq_next(struct seq_file *seq, void *v, loff_t *pos)
{
	struct mfc_cache *mfc = v;
	struct ipmr_mfc_iter *it = seq->private;

	++*pos;

	if (v == SEQ_START_TOKEN)
		return ipmr_mfc_seq_idx(seq->private, 0);

	if (mfc->next)
		return mfc->next;
	
	if (it->cache == &mfc_unres_queue) 
		goto end_of_list;

	BUG_ON(it->cache != mfc_cache_array);

	while (++it->ct < MFC_LINES) {
		mfc = mfc_cache_array[it->ct];
		if (mfc)
			return mfc;
	}

	/* exhausted cache_array, show unresolved */
	read_unlock(&mrt_lock);
	it->cache = &mfc_unres_queue;
	it->ct = 0;
		
	spin_lock_bh(&mfc_unres_lock);
	mfc = mfc_unres_queue;
	if (mfc) 
		return mfc;

 end_of_list:
	spin_unlock_bh(&mfc_unres_lock);
	it->cache = NULL;

	return NULL;
}

static void ipmr_mfc_seq_stop(struct seq_file *seq, void *v)
{
	struct ipmr_mfc_iter *it = seq->private;

	if (it->cache == &mfc_unres_queue)
		spin_unlock_bh(&mfc_unres_lock);
	else if (it->cache == mfc_cache_array)
		read_unlock(&mrt_lock);
}

static int ipmr_mfc_seq_show(struct seq_file *seq, void *v)
{
	int n;

	if (v == SEQ_START_TOKEN) {
		seq_puts(seq, 
		 "Group    Origin   Iif     Pkts    Bytes    Wrong Oifs\n");
	} else {
		const struct mfc_cache *mfc = v;
		const struct ipmr_mfc_iter *it = seq->private;
		
		seq_printf(seq, "%08lX %08lX %-3d %8ld %8ld %8ld",
			   (unsigned long) mfc->mfc_mcastgrp,
			   (unsigned long) mfc->mfc_origin,
			   mfc->mfc_parent,
			   mfc->mfc_un.res.pkt,
			   mfc->mfc_un.res.bytes,
			   mfc->mfc_un.res.wrong_if);

		if (it->cache != &mfc_unres_queue) {
			for(n = mfc->mfc_un.res.minvif; 
			    n < mfc->mfc_un.res.maxvif; n++ ) {
				if(VIF_EXISTS(n) 
				   && mfc->mfc_un.res.ttls[n] < 255)
				seq_printf(seq, 
					   " %2d:%-3d", 
					   n, mfc->mfc_un.res.ttls[n]);
			}
		}
		seq_putc(seq, '\n');
	}
	return 0;
}

static struct seq_operations ipmr_mfc_seq_ops = {
	.start = ipmr_mfc_seq_start,
	.next  = ipmr_mfc_seq_next,
	.stop  = ipmr_mfc_seq_stop,
	.show  = ipmr_mfc_seq_show,
};

static int ipmr_mfc_open(struct inode *inode, struct file *file)
{
	struct seq_file *seq;
	int rc = -ENOMEM;
	struct ipmr_mfc_iter *s = kmalloc(sizeof(*s), GFP_KERNEL);
       
	if (!s)
		goto out;

	rc = seq_open(file, &ipmr_mfc_seq_ops);
	if (rc)
		goto out_kfree;

	seq = file->private_data;
	seq->private = s;
out:
	return rc;
out_kfree:
	kfree(s);
	goto out;

}

static struct file_operations ipmr_mfc_fops = {
	.owner	 = THIS_MODULE,
	.open    = ipmr_mfc_open,
	.read    = seq_read,
	.llseek  = seq_lseek,
	.release = seq_release_private,
};
#endif	

#ifdef CONFIG_IP_PIMSM_V2
static struct net_protocol pim_protocol = {
	.handler	=	pim_rcv,
};
#endif


/*
 *	Setup for IP multicast routing
 */
 
void __init ip_mr_init(void) //为ip组播建立环境 包括创建组播转发缓存池 为临时路由转发缓存建立定时器等 ip_mr_init在 inet_init中被调 用以初始化ip组播
{
	mrt_cachep = kmem_cache_create("ip_mrt_cache", //为组播缓存池mrt_cachep分配空间 通过slab缓存池来分配固定长度的空间 可以极大提高性能并消除碎片
								   sizeof(struct mfc_cache),
				       0, SLAB_HWCACHE_ALIGN|SLAB_PANIC,
				       NULL, NULL);
	init_timer(&ipmr_expire_timer); //初始化临时路由转发缓存的定时器 通过定时器 可以删除在规定时间内未添加组播转发缓存对应的临时路由转发缓存
	ipmr_expire_timer.function=ipmr_expire_process;
	register_netdevice_notifier(&ip_mr_notifier); //将ip_mr_notifier注册到网卡通知连中 这样当网卡状态发生变化时 可以及时响应
#ifdef CONFIG_PROC_FS	
	proc_net_fops_create("ip_mr_vif", 0, &ipmr_vif_fops); //如果编译时 设置了支持proc文件系统 则在proc文件系统中创建ip_mr_vif和ip_mr_cache节点 之后可以通过这两个文件查看虚拟接口和组播转发缓存的相关信息
	proc_net_fops_create("ip_mr_cache", 0, &ipmr_mfc_fops);
#endif	
}

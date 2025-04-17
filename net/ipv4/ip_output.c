/*
 * INET		An implementation of the TCP/IP protocol suite for the LINUX
 *		operating system.  INET is implemented using the  BSD Socket
 *		interface as the means of communication with the user level.
 *
 *		The Internet Protocol (IP) output module.
 *
 * Version:	$Id: ip_output.c,v 1.100 2002/02/01 22:01:03 davem Exp $
 *
 * Authors:	Ross Biro
 *		Fred N. van Kempen, <waltje@uWalt.NL.Mugnet.ORG>
 *		Donald Becker, <becker@super.org>
 *		Alan Cox, <Alan.Cox@linux.org>
 *		Richard Underwood
 *		Stefan Becker, <stefanb@yello.ping.de>
 *		Jorge Cwik, <jorge@laser.satlink.net>
 *		Arnt Gulbrandsen, <agulbra@nvg.unit.no>
 *		Hirokazu Takahashi, <taka@valinux.co.jp>
 *
 *	See ip_input.c for original log
 *
 *	Fixes:
 *		Alan Cox	:	Missing nonblock feature in ip_build_xmit.
 *		Mike Kilburn	:	htons() missing in ip_build_xmit.
 *		Bradford Johnson:	Fix faulty handling of some frames when 
 *					no route is found.
 *		Alexander Demenshin:	Missing sk/skb free in ip_queue_xmit
 *					(in case if packet not accepted by
 *					output firewall rules)
 *		Mike McLagan	:	Routing by source
 *		Alexey Kuznetsov:	use new route cache
 *		Andi Kleen:		Fix broken PMTU recovery and remove
 *					some redundant tests.
 *	Vitaly E. Lavrov	:	Transparent proxy revived after year coma.
 *		Andi Kleen	: 	Replace ip_reply with ip_send_reply.
 *		Andi Kleen	:	Split fast and slow ip_build_xmit path 
 *					for decreased register pressure on x86 
 *					and more readibility. 
 *		Marc Boucher	:	When call_out_firewall returns FW_QUEUE,
 *					silently drop skb instead of failing with -EPERM.
 *		Detlev Wengorz	:	Copy protocol for fragments.
 *		Hirokazu Takahashi:	HW checksumming for outgoing UDP
 *					datagrams.
 *		Hirokazu Takahashi:	sendfile() on UDP works now.
 */

#include <asm/uaccess.h>
#include <asm/system.h>
#include <linux/module.h>
#include <linux/types.h>
#include <linux/kernel.h>
#include <linux/sched.h>
#include <linux/mm.h>
#include <linux/string.h>
#include <linux/errno.h>
#include <linux/highmem.h>

#include <linux/socket.h>
#include <linux/sockios.h>
#include <linux/in.h>
#include <linux/inet.h>
#include <linux/netdevice.h>
#include <linux/etherdevice.h>
#include <linux/proc_fs.h>
#include <linux/stat.h>
#include <linux/init.h>

#include <net/snmp.h>
#include <net/ip.h>
#include <net/protocol.h>
#include <net/route.h>
#include <net/xfrm.h>
#include <linux/skbuff.h>
#include <net/sock.h>
#include <net/arp.h>
#include <net/icmp.h>
#include <net/checksum.h>
#include <net/inetpeer.h>
#include <net/checksum.h>
#include <linux/igmp.h>
#include <linux/netfilter_ipv4.h>
#include <linux/netfilter_bridge.h>
#include <linux/mroute.h>
#include <linux/netlink.h>
#include <linux/tcp.h>

int sysctl_ip_default_ttl __read_mostly = IPDEFTTL;

/* Generate a checksum for an outgoing IP datagram. */
__inline__ void ip_send_check(struct iphdr *iph)
{
	iph->check = 0;
	iph->check = ip_fast_csum((unsigned char *)iph, iph->ihl);
}

/* dev_loopback_xmit for use with netfilter. */
static int ip_dev_loopback_xmit(struct sk_buff *newskb)
{
	newskb->mac.raw = newskb->data;
	__skb_pull(newskb, newskb->nh.raw - newskb->data);
	newskb->pkt_type = PACKET_LOOPBACK;
	newskb->ip_summed = CHECKSUM_UNNECESSARY;
	BUG_TRAP(newskb->dst);
	netif_rx(newskb);
	return 0;
}

static inline int ip_select_ttl(struct inet_sock *inet, struct dst_entry *dst)
{
	int ttl = inet->uc_ttl;

	if (ttl < 0)
		ttl = dst_metric(dst, RTAX_HOPLIMIT);
	return ttl;
}

/* 
 *		Add an ip header to a skbuff and send it out.
 *
 */
int ip_build_and_send_pkt(struct sk_buff *skb/*待封装成ip包的tcp段*/, struct sock *sk/*输出该tcp段的传输控制块*/,
			  __be32 saddr/*输出该tcp段的源ip*/, __be32 daddr, struct ip_options *opt/*ip选项信息*/) //tcp建链过程中 打包输出syn + ack类型的tcp段
{
	struct inet_sock *inet = inet_sk(sk);
	struct rtable *rt = (struct rtable *)skb->dst;
	struct iphdr *iph;

	/* Build the IP header. */
	if (opt)
		iph=(struct iphdr *)skb_push(skb,sizeof(struct iphdr) + opt->optlen); //为数据包建立ip首部 如果存在ip选项则ip首部长度适当增加
	else
		iph=(struct iphdr *)skb_push(skb,sizeof(struct iphdr));

	iph->version  = 4; //设置ip首部各字段
	iph->ihl      = 5;
	iph->tos      = inet->tos;
	if (ip_dont_fragment(sk, &rt->u.dst)) //frag_off根据输出套接字的pmtudisc值来设置
		iph->frag_off = htons(IP_DF);
	else
		iph->frag_off = 0;
	iph->ttl      = ip_select_ttl(inet, &rt->u.dst);
	iph->daddr    = rt->rt_dst;
	iph->saddr    = rt->rt_src;
	iph->protocol = sk->sk_protocol;
	iph->tot_len  = htons(skb->len);
	ip_select_ident(iph, &rt->u.dst, sk); //id取值根据ip数据包是否分片不同 不分片的id取自套接字中的id成员  ip分片则从对端信息块的ip_id_count中获取
	skb->nh.iph   = iph;

	if (opt && opt->optlen) { //如果存在ip选项 则在ip数据包首部构建ip选项
		iph->ihl += opt->optlen>>2;
		ip_options_build(skb, opt, daddr, rt, 0);
	}
	ip_send_check(iph); //为ip数据包计算校验和

	skb->priority = sk->sk_priority; //设置输出数据包的QoS类别

	/* Send it out. */
	return NF_HOOK(PF_INET, NF_IP_LOCAL_OUT, skb, NULL, rt->u.dst.dev, //通过netfilter处理后 调dst_output处理数据包的输出
		       dst_output);
}

EXPORT_SYMBOL_GPL(ip_build_and_send_pkt);

static inline int ip_finish_output2(struct sk_buff *skb)            // 通过邻居子系统将数据包输出到网卡
{
	struct dst_entry *dst = skb->dst;
	struct net_device *dev = dst->dev;
	int hh_len = LL_RESERVED_SPACE(dev);

	/* Be paranoid, rather than too clever. */
	if (unlikely(skb_headroom(skb) < hh_len && dev->hard_header)) { // 检查skb的前部空间是否还能存储链路层首部 不够则重新分配更大skb & 释放源skb
		struct sk_buff *skb2;

		skb2 = skb_realloc_headroom(skb, LL_RESERVED_SPACE(dev));
		if (skb2 == NULL) {
			kfree_skb(skb);
			return -ENOMEM;
		}
		if (skb->sk)
			skb_set_owner_w(skb2, skb->sk);
		kfree_skb(skb);
		skb = skb2;
	}

	if (dst->hh)
		return neigh_hh_output(dst->hh, skb);                       // 如果缓存了链路层首部 则调neigh_hh_output输出数据包 否则若存在对应的邻居项 则通过邻居项的输出方法输出数据包
	else if (dst->neighbour)
		return dst->neighbour->output(skb);

	if (net_ratelimit())                                            // 既没有链路层首部 又没有对应的邻居项 则不能输出 释放该报
		printk(KERN_DEBUG "ip_finish_output2: No header cache and no neighbour!\n");
	kfree_skb(skb);
	return -EINVAL;
}

static inline int ip_finish_output(struct sk_buff *skb)             // 经netfilter处理后 调ip_finish_output继续ip数据包的输出
{
#if defined(CONFIG_NETFILTER) && defined(CONFIG_XFRM)
	/* Policy lookup after SNAT yielded a new policy */
	if (skb->dst->xfrm != NULL) {
		IPCB(skb)->flags |= IPSKB_REROUTED;
		return dst_output(skb);
	}
#endif
	if (skb->len > dst_mtu(skb->dst) && !skb_is_gso(skb))           // 如果数据包大于MTU 则调ip_fragment分片 否则调ip_finish_output2
		return ip_fragment(skb, ip_finish_output2);
	else
		return ip_finish_output2(skb);                              // 通过邻居子系统将数据包输出到网卡
}

int ip_mc_output(struct sk_buff *skb) //对于从本地输出或是需进行转发的组播报文 如果输出路由查找成功 便可以输出 输出处理函数为ip_mc_output
{
	struct sock *sk = skb->sk;
	struct rtable *rt = (struct rtable*)skb->dst;
	struct net_device *dev = rt->u.dst.dev;

	/*
	 *	If the indicated interface is up and running, send the packet.
	 */
	IP_INC_STATS(IPSTATS_MIB_OUTREQUESTS);

	skb->dev = dev;                     // dev 由路由决定
	skb->protocol = htons(ETH_P_IP); //设置输出报文的输出网卡设备及协议

	/*
	 *	Multicasts are looped back for other local users
	 */

	if (rt->rt_flags&RTCF_MULTICAST) { //在以下条件下需复制一份报文输出到回环接口
		if ((!sk || inet_sk(sk)->mc_loop) //1组播报文无宿主 即不是从本地输出的组播报文 2组播报文需要发送回路 3在编译支持ip组播的情况下 同时该组播报文是输入到本地的 4组播报文还未转发
#ifdef CONFIG_IP_MROUTE
		/* Small optimization: do not loopback not local frames,
		   which returned after forwarding; they will be  dropped
		   by ip_mr_input in any case.
		   Note, that local frames are looped back to be delivered
		   to local recipients.

		   This check is duplicated in ip_mr_input at the moment.
		 */
		    && ((rt->rt_flags&RTCF_LOCAL) || !(IPCB(skb)->flags&IPSKB_FORWARDED))
#endif
		) {
			struct sk_buff *newskb = skb_clone(skb, GFP_ATOMIC);
			if (newskb)
				NF_HOOK(PF_INET, NF_IP_POST_ROUTING, newskb, NULL,
					newskb->dev, 
					ip_dev_loopback_xmit);
		}

		/* Multicasts with ttl 0 must not go beyond the host */

		if (skb->nh.iph->ttl == 0) { //若待输出组播报文的ttl为0 则将其释放
			kfree_skb(skb);
			return 0;
		}
	}

	if (rt->rt_flags&RTCF_BROADCAST) {
		struct sk_buff *newskb = skb_clone(skb, GFP_ATOMIC);
		if (newskb)
			NF_HOOK(PF_INET, NF_IP_POST_ROUTING, newskb, NULL,
				newskb->dev, ip_dev_loopback_xmit);
	}

	return NF_HOOK_COND(PF_INET, NF_IP_POST_ROUTING, skb, NULL, skb->dev, //如果输出路由类型为广播类型 则需复制一份发给回环设备
			    ip_finish_output,
			    !(IPCB(skb)->flags & IPSKB_REROUTED)); //最后通过netfilter模块处理后 调ip_finish_output将该组播报文输出
}

int ip_output(struct sk_buff *skb)                          // 对于单播数据包 目的路由缓存项中的output 就是ip_output
{
	struct net_device *dev = skb->dst->dev;

	IP_INC_STATS(IPSTATS_MIB_OUTREQUESTS);

	skb->dev = dev;
	skb->protocol = htons(ETH_P_IP);                        // 设置数据包的输出网卡和数据包网络层协议类型

	return NF_HOOK_COND(PF_INET, NF_IP_POST_ROUTING, skb, NULL, dev,
		            ip_finish_output,
			    !(IPCB(skb)->flags & IPSKB_REROUTED));      // 经netfilter处理后 调ip_finish_output继续ip数据包的输出
}

int ip_queue_xmit(struct sk_buff *skb/*待封装成ip报的tcp段*/, int ipfragok)         // 将tcp段打包成ip报的最常用方法
{
	struct sock *sk = skb->sk;
	struct inet_sock *inet = inet_sk(sk);
	struct ip_options *opt = inet->opt;
	struct rtable *rt;
	struct iphdr *iph;

	/* Skip all of this if the packet is already routed,
	 * f.e. by something like SCTP.
	 */
	rt = (struct rtable *) skb->dst;                                                // 如果待输出的数据包已准备好路由缓存 则无需再查找路由 直接跳到packet_routed处理
	if (rt != NULL)
		goto packet_routed;

	/* Make sure we can route this packet. */
	rt = (struct rtable *)__sk_dst_check(sk, 0);                                    // 如果该数据包的传输控制块中缓存了输出路由缓存项 则需检测该路由缓存项 是否过期
	if (rt == NULL) {
		__be32 daddr;

		/* Use correct destination address if we have options. */
		daddr = inet->daddr;
		if(opt && opt->srr)                                                         // 如果使用源地址路由 下一跳为inet->opt->faddr 即选项中的第一个地址
			daddr = opt->faddr;

		{
			struct flowi fl = { .oif = sk->sk_bound_dev_if,                         // 过期则 重新通过输出网卡 目的地址 源地址 等信息重新查找路由缓存项 找到相应的路由缓存项则将其缓存到传输控制块中 否则丢弃
					    .nl_u = { .ip4_u =
						      { .daddr = daddr,
							.saddr = inet->saddr,
							.tos = RT_CONN_FLAGS(sk) } },
					    .proto = sk->sk_protocol,
					    .uli_u = { .ports =
						       { .sport = inet->sport,
							 .dport = inet->dport } } };

			/* If this fails, retransmit mechanism of transport layer will
			 * keep trying until route appears or the connection times
			 * itself out.
			 */
			security_sk_classify_flow(sk, &fl);
			if (ip_route_output_flow(&rt, &fl, sk, 0))
				goto no_route;
		}
		sk_setup_caps(sk, &rt->u.dst);                                              // 未过期 则直接用传输控制块中的路由缓存项目
	}
	skb->dst = dst_clone(&rt->u.dst);

packet_routed:
	if (opt && opt->is_strictroute && rt->rt_dst != rt->rt_gateway)                 // 查找到输出路由后 先进行严格的源路由选项处理 如果存在严格源路由选项 & 数据包的下一跳地址和网关不一致则丢弃
		goto no_route;

	/* OK, we know where to send it, allocate and build IP header. */
	iph = (struct iphdr *) skb_push(skb, sizeof(struct iphdr) + (opt ? opt->optlen : 0)); //设置ip首部中各字段的值 如果存在ip选项 则在ip数据包首部中构建ip选项
	*((__be16 *)iph) = htons((4 << 12) | (5 << 8) | (inet->tos & 0xff));
	iph->tot_len = htons(skb->len);
	if (ip_dont_fragment(sk, &rt->u.dst) && !ipfragok)
		iph->frag_off = htons(IP_DF);
	else
		iph->frag_off = 0;
	iph->ttl      = ip_select_ttl(inet, &rt->u.dst);
	iph->protocol = sk->sk_protocol;
	iph->saddr    = rt->rt_src;
	iph->daddr    = rt->rt_dst;
	skb->nh.iph   = iph;
	/* Transport layer set skb->h.foo itself. */

	if (opt && opt->optlen) {
		iph->ihl += opt->optlen >> 2;
		ip_options_build(skb, opt, inet->daddr, rt, 0);
	}

	ip_select_ident_more(iph, &rt->u.dst, sk,
			     (skb_shinfo(skb)->gso_segs ?: 1) - 1);

	/* Add an IP checksum. */
	ip_send_check(iph);

	skb->priority = sk->sk_priority; //QoS

	return NF_HOOK(PF_INET, NF_IP_LOCAL_OUT, skb, NULL, rt->u.dst.dev,              // 通过netfilter处理后 由dst_output(即ip_output)处理数据包的输出
		       dst_output);

no_route:
	IP_INC_STATS(IPSTATS_MIB_OUTNOROUTES);                                          // 找不到路由缓存项 则丢弃该数据包
	kfree_skb(skb);
	return -EHOSTUNREACH;
}


static void ip_copy_metadata(struct sk_buff *to, struct sk_buff *from)
{
	to->pkt_type = from->pkt_type;
	to->priority = from->priority;
	to->protocol = from->protocol;
	dst_release(to->dst);
	to->dst = dst_clone(from->dst);
	to->dev = from->dev;
	to->mark = from->mark;

	/* Copy the flags to each fragment. */
	IPCB(to)->flags = IPCB(from)->flags;

#ifdef CONFIG_NET_SCHED
	to->tc_index = from->tc_index;
#endif
#ifdef CONFIG_NETFILTER
	/* Connection association is same as pre-frag packet */
	nf_conntrack_put(to->nfct);
	to->nfct = from->nfct;
	nf_conntrack_get(to->nfct);
	to->nfctinfo = from->nfctinfo;
#if defined(CONFIG_IP_VS) || defined(CONFIG_IP_VS_MODULE)
	to->ipvs_property = from->ipvs_property;
#endif
#ifdef CONFIG_BRIDGE_NETFILTER
	nf_bridge_put(to->nf_bridge);
	to->nf_bridge = from->nf_bridge;
	nf_bridge_get(to->nf_bridge);
#endif
#endif
	skb_copy_secmark(to, from);
}

/*
 *	This IP datagram is too large to be sent in one piece.  Break it up into
 *	smaller pieces (each of size equal to IP header plus
 *	a block of the data of the original IP data part) that will yet fit in a
 *	single device frame, and queue such a frame for sending.
 */

int ip_fragment(struct sk_buff *skb, int (*output)(struct sk_buff*)) //skb长度大于mtu
{
	struct iphdr *iph;
	int raw = 0;
	int ptr;
	struct net_device *dev;
	struct sk_buff *skb2;
	unsigned int mtu, hlen, left, len, ll_rs, pad;
	int offset;
	__be16 not_last_frag;
	struct rtable *rt = (struct rtable*)skb->dst;
	int err = 0;

	dev = rt->u.dst.dev;

	/*
	 *	Point into the IP datagram header.
	 */

	iph = skb->nh.iph; //获取待分片的ip包的ip首部

	if (unlikely((iph->frag_off & htons(IP_DF)) && !skb->local_df)) { //如果df为真 则发送一个因为需要分片而设置了df标志的目的不可达icmp报文&丢弃报文 设置ip状态为分片失败 释放skb 返回消息过长错误码
		IP_INC_STATS(IPSTATS_MIB_FRAGFAILS);
		icmp_send(skb, ICMP_DEST_UNREACH, ICMP_FRAG_NEEDED,
			  htonl(dst_mtu(&rt->u.dst)));
		kfree_skb(skb);
		return -EMSGSIZE;
	}

	/*
	 *	Setup starting values.
	 */

	hlen = iph->ihl * 4; //获取待分片ip包的ip首部长度&扣除了ip首部长度的mtu值
	mtu = dst_mtu(&rt->u.dst) - hlen;	/* Size of data space */
	IPCB(skb)->flags |= IPSKB_FRAG_COMPLETE; //在分片之前先给ip数据包控制块设置ipskb_frag_complete标志 标识完成分片

	/* When frag_list is given, use it. First, check its validity:               //快速分片即传输层已分好了&将这些块连在skb_shinfo(skb)->frag_list 此时可以通过快速分片处理
	 * some transformers could create wrong frag_list or break existing
	 * one, it is not prohibited. In this case fall back to copying.
	 *
	 * LATER: this step can be merged to real generation of fragments,
	 * we can switch to copy when see the first bad fragment.
	 */
	if (skb_shinfo(skb)->frag_list) { //判断此ip包是否支持快速分片 即如果该数据包第一个skb的skb_shared_info结构中的frag_list链上有分片的skb 即说明传输层已备好了分好的片
		struct sk_buff *frag;
		int first_len = skb_pagelen(skb); //获取ip包第一个分片数据长度 包括sg类型聚合分散io数据区中的数据

		if (first_len - hlen > mtu || //对第一个分片做检测 要进行快速分片 还需要对传输层传递的所有skb做一些判断 在以下四种情况下不能快分
		    ((first_len - hlen) & 7) || //1有分片长度大于mtu 2除最后一个分片外还有分片长度未8字节对齐 3ip首部中的mf或片偏移不为0 说明skb不是完整数据包 4此skb被克隆
		    (iph->frag_off & htons(IP_MF|IP_OFFSET)) ||
		    skb_cloned(skb))
			goto slow_path;

		for (frag = skb_shinfo(skb)->frag_list; frag; frag = frag->next) { //遍历后续所有分片 做相关设置
			/* Correct geometry. */
			if (frag->len > mtu || //在遍历分片中 要继续对分片做校验 包括分片的长度是否超过mtu 不是最后一个分片的长度是否8字节对齐 缓存区头部是否有足够空间存放ip首部 否则不适合快分
			    ((frag->len & 7) && frag->next) || //对分片检验 有三种情况下不能块分 1分片长度大于mtu 2未8字节对齐除最后一个分片 3没有为二层首部留足够空间
			    skb_headroom(frag) < hlen)
			    goto slow_path;

			/* Partially cloned skb? */
			if (skb_shared(frag)) //判断每个分片是否被克隆
				goto slow_path;

			BUG_ON(frag->sk);
			if (skb->sk) { //递增数据包所属传输控制块引用计数  当前分片的传输控制块字段指向该传输控制块 然后设置skb释放回调函数 最后修改第一个分片的缓存区总长度 减去当前分片长度
				sock_hold(skb->sk);
				frag->sk = skb->sk;
				frag->destructor = sock_wfree;
				skb->truesize -= frag->truesize;
			}
		}

		/* Everything is OK. Generate! */

		err = 0; //初始化错误码&分片偏移
		offset = 0;
		frag = skb_shinfo(skb)->frag_list; //保存frag_list指针 并将该指针置NULL 分片以后每个片都将是一个独立的ip数据包 因此在此将原来链接在第一个分片frag_list上的所有后续分片skb取下 同时为了进一步对这些后继分片skb进行处理 需要保存该指针
		skb_shinfo(skb)->frag_list = NULL;
		skb->data_len = first_len - skb_headlen(skb); //重置第一个分片的数据长度&缓冲区长度
		skb->len = first_len;
		iph->tot_len = htons(first_len);
		iph->frag_off = htons(IP_MF); //设置第一个分片ip首部中的总长度字段&mf标志
		ip_send_check(iph); //重新计算第一个分片的ip首部校验和

		for (;;) { //从第二个分片开始循环设置每个分片的skb&ip首部 然后将所有分片都发出去
			/* Prepare header of the next frame,
			 * before previous one went down. */
			if (frag) { //在发送当前分片前 需完成对后一个分片的相应设置 其中一些是根据当前分片来设置的
				frag->ip_summed = CHECKSUM_NONE; //设置后一个分片的校验和完全由软件处理
				frag->h.raw = frag->data; //设置后一个分片skb中指向三层&四层首部的指针
				frag->nh.raw = __skb_push(frag, hlen);
				memcpy(frag->nh.raw, iph, hlen); //将当前分片的ip首部复制给后一个分片 并修改后一个分片ip首部的总长度字段
				iph = frag->nh.iph;
				iph->tot_len = htons(frag->len);
				ip_copy_metadata(frag, skb); //根据当前分片skb填充后一个skb分片中的参数
				if (offset == 0) //如果是在处理第一个分片 则调ip_options_fragment将第二个分片skb中无需复制到每个分片的ip选项都填充为ioopt_noop 此后所有的分片选项部分都简单的复制上一个即可
					ip_options_fragment(frag);
				offset += skb->len - hlen;
				iph->frag_off = htons(offset>>3); //设置后一个分片的ip首部片偏移值 mf标志 及校验和
				if (frag->next != NULL)
					iph->frag_off |= htons(IP_MF);
				/* Ready, complete checksum */
				ip_send_check(iph); //
			}

			err = output(skb); //调用参数中给出的输出回调函数output 将当前分片发送出去

			if (!err) //对mib的ipstats_mib_fragcreates数据进行统计
				IP_INC_STATS(IPSTATS_MIB_FRAGCREATES);
			if (err || !frag) //如果发送当前分片失败 | 无后续分片 则结束分片和发送 即一旦一个分片发送失败则剩余分片都将不发送
				break;

			skb = frag;
			frag = skb->next; //从链表取下一个待处理分片
			skb->next = NULL;
		}

		if (err == 0) { //如果发送成功所有分片 则对MIB的IOSTATS_MIB_FRAGOKS数据进行统计后返回
			IP_INC_STATS(IPSTATS_MIB_FRAGOKS);
			return 0;
		}

		while (frag) { //如果所有分片发送失败 则释放所有未发送ip分片 对mib的ipstats_mib_fragfails数据进行统计后返回
			skb = frag->next;
			kfree_skb(frag);
			frag = skb;
		}
		IP_INC_STATS(IPSTATS_MIB_FRAGFAILS);
		return err;
	}

slow_path:
	left = skb->len - hlen;		/* Space per frame */ //获取待分片的ip数据包长度 此处减去hlen是为二层首部留出空间
	ptr = raw + hlen;		/* Where to start from */ //获取ip数据包中数据区指针

	/* for bridged IP traffic encapsulated inside f.e. a vlan header,
	 * we need to make room for the encapsulating header
	 */
	pad = nf_bridge_pad(skb); //如果是桥转发基于vlan的ip数据包 则需获得vlan首部长度 在后面分配skb缓存区时留下相应的空间 同时还需修改mtu
	ll_rs = LL_RESERVED_SPACE_EXTRA(rt->u.dst.dev, pad); //获得二层首部长度
	mtu -= pad;

	/*
	 *	Fragment the datagram.
	 */

	offset = (ntohs(iph->frag_off) & IP_OFFSET) << 3;
	not_last_frag = iph->frag_off & htons(IP_MF); //取得mf位值 mf值除最后一个分片外都应该置1 表示该分片之后还有分片

	/*
	 *	Keep copying data until we run out.
	 */

	while(left > 0)	{
		len = left; //循环对left长度的数据进行分片 为每个分片创建一个新的skb
		/* IF: it doesn't fit, use 'mtu' - the data space left */
		if (len > mtu) //如果剩余长度大于mtu 则以mtu为分片长度
			len = mtu;
		/* IF: we are not sending upto and including the packet end
		   then align the next start on an eight byte boundary */
		if (len < left)	{ //除非最后一个分片 否则分配不包括ip首部长度部分 需8字节对齐
			len &= ~7;
		}
		/*
		 *	Allocate buffer.
		 */

		if ((skb2 = alloc_skb(len+hlen+ll_rs, GFP_ATOMIC)) == NULL) { //为分片分配一个skb 其长度为分片长+ip首部长+二层首部长
			NETDEBUG(KERN_INFO "IP: frag: no memory for new fragment!\n");
			err = -ENOMEM;
			goto fail;
		}

		/*
		 *	Set up data on packet
		 */

		ip_copy_metadata(skb2, skb); //根据原始数据包skb填充分片新分配的skb 包括类型优先级协议等
		skb_reserve(skb2, ll_rs); //分别为二层首部 分片加ip首部留出相应的空间和数据空间 以备后面填充数据
		skb_put(skb2, len + hlen); //设置新skb中三层首部指针和四层首部指针
		skb2->nh.raw = skb2->data;
		skb2->h.raw = skb2->data + hlen;

		/*
		 *	Charge the memory for the fragment to any owner
		 *	it might possess
		 */

		if (skb->sk) //设置新skb宿主 包括递增数据包传输控制块的引用数 设置skb的释放回调函数等
			skb_set_owner_w(skb2, skb->sk);

		/*
		 *	Copy the packet header into the new buffer.
		 */

		memcpy(skb2->nh.raw, skb->data, hlen); //复制ip首部到新skb中

		/*
		 *	Copy a block of the IP datagram.
		 */
		if (skb_copy_bits(skb, ptr, skb2->h.raw, len)) //复制分片数据&更新原始数据包剩余未分片数量 调的是skb_copy_bits 而非memcpy
			BUG();
		left -= len;

		/*
		 *	Fill in the new header fields.
		 */
		iph = skb2->nh.iph;
		iph->frag_off = htons((offset >> 3)); //设置分片的片偏移字段 对于第一个分片 该值即原始ip数据包的片偏移字段

		/* ANK: dirty, but effective trick. Upgrade options only if
		 * the segment to be fragmented was THE FIRST (otherwise,
		 * options are already fixed) and make it ONCE
		 * on the initial skb, so that all the following fragments
		 * will inherit fixed options.
		 */
		if (offset == 0) //根据条件清理掉ip选项中的一些选项 设置为ipopt_noop 因为这些选项只要针对一个ip数据包处理一次即可 没必要每个分片都处理
			ip_options_fragment(skb); //第一个分片的ip选项是完整的 而其余分片只存在某些选项 因此其余分片中无需复制到分片的ip选项都为ipopt_noop

		/*
		 *	Added AC : If we are fragmenting a fragment that's not the
		 *		   last fragment then keep MF on each bit
		 */
		if (left > 0 || not_last_frag) //如果不是最后一个分片 则设置ip首部中标识字段的mf位
			iph->frag_off |= htons(IP_MF);
		ptr += len; //更新后一个分片在整个原始数据包中的偏移 & 后一个分片在当前被分片数据包中的偏移量   这两个偏移量是有区别的 因为一个数据包在传输过程中可能被多次分片 因此当前被分片的数据包也有可能是另一个数据包分片
		offset += len;

		/*
		 *	Put this fragment into the sending queue.
		 */
		iph->tot_len = htons(len + hlen); //设置ip首部中总长度字段

		ip_send_check(iph); //重新计算该分片的ip首部校验和

		err = output(skb2); //调用参数中给出的输出回调函数output 将当前分片发出去
		if (err)
			goto fail;

		IP_INC_STATS(IPSTATS_MIB_FRAGCREATES); //对mib的ipstats_mib_fragcreates数据进行统计
	}
	kfree_skb(skb);
	IP_INC_STATS(IPSTATS_MIB_FRAGOKS); //完成所有分片&发送后 释放被分片的ip数据包 同时对mib的ipstats_mib_fragoks数据进行统计
	return err;

fail:
	kfree_skb(skb); 
	IP_INC_STATS(IPSTATS_MIB_FRAGFAILS);
	return err;
}

EXPORT_SYMBOL(ip_fragment);

int
ip_generic_getfrag(void *from, char *to, int offset, int len, int odd, struct sk_buff *skb)
{
	struct iovec *iov = from;

	if (skb->ip_summed == CHECKSUM_PARTIAL) {
		if (memcpy_fromiovecend(to, iov, offset, len) < 0)
			return -EFAULT;
	} else {
		__wsum csum = 0;
		if (csum_partial_copy_fromiovecend(to, iov, offset, len, &csum) < 0)
			return -EFAULT;
		skb->csum = csum_block_add(skb->csum, csum, odd);
	}
	return 0;
}

static inline __wsum
csum_page(struct page *page, int offset, int copy)
{
	char *kaddr;
	__wsum csum;
	kaddr = kmap(page);
	csum = csum_partial(kaddr + offset, copy, 0);
	kunmap(page);
	return csum;
}

static inline int ip_ufo_append_data(struct sock *sk, //实现了 复制数据到输出队列末尾那个skb的聚合分散io页面中
			int getfrag(void *from, char *to, int offset, int len,
			       int odd, struct sk_buff *skb),
			void *from, int length, int hh_len, int fragheaderlen,
			int transhdrlen, int mtu,unsigned int flags)
{
	struct sk_buff *skb;
	int err;

	/* There is support for UDP fragmentation offload by network
	 * device, so create one single skb packet containing complete
	 * udp datagram
	 */
	if ((skb = skb_peek_tail(&sk->sk_write_queue)) == NULL) { //如果输出队列不空 则获取输出队列末尾那个skb 否则分配新的skb & 为新分配的skb在线性空间中保留出链路层 网络层 传输层首部空间 然后初始化skb相关校验信息 初始化传输控制块的sk_sndmsg_off表示分片内没有数据
		skb = sock_alloc_send_skb(sk,
			hh_len + fragheaderlen + transhdrlen + 20,
			(flags & MSG_DONTWAIT), &err);

		if (skb == NULL)
			return err;

		/* reserve space for Hardware header */
		skb_reserve(skb, hh_len);

		/* create space for UDP/IP header */
		skb_put(skb,fragheaderlen + transhdrlen);

		/* initialize network header pointer */
		skb->nh.raw = skb->data;

		/* initialize protocol header pointer */
		skb->h.raw = skb->data + fragheaderlen;

		skb->ip_summed = CHECKSUM_PARTIAL;
		skb->csum = 0;
		sk->sk_sndmsg_off = 0;
	}

	err = skb_append_datato_frags(sk,skb, getfrag, from, //将数据复制到聚合分散io页面中 若复制成功 则设置skb的gso_size和gso_type 然后将skb添加到输出队列末尾 否则释放该skb
			       (length - transhdrlen));
	if (!err) {
		/* specify the length of each IP datagram fragment*/
		skb_shinfo(skb)->gso_size = mtu - fragheaderlen;
		skb_shinfo(skb)->gso_type = SKB_GSO_UDP;
		__skb_queue_tail(&sk->sk_write_queue, skb);

		return 0;
	}
	/* There is not enough support do UFO ,
	 * so follow normal path
	 */
	kfree_skb(skb);
	return err;
}

/*
 *	ip_append_data() and ip_append_page() can make one large IP datagram
 *	from many pieces of data. Each pieces will be holded on the socket
 *	until ip_push_pending_frames() is called. Each piece can be a page
 *	or non-page data.
 *	
 *	Not only UDP, other transport protocols - e.g. raw sockets - can use
 *	this interface potentially.
 *
 *	LATER: length must be adjusted by pad at tail, when it is required.
 */
int ip_append_data(struct sock *sk/*输出数据的传输控制块 */,
		   int getfrag(void *from, char *to, int offset, int len,
			       int odd/*从上一个skb中剩余下来并复制到此skb中的数据长度  如果是奇数则后续数据校验和的计算时的16位数据的高8低8是颠倒的 因此需要对调*/,
			       struct sk_buff *skb/*复制数据的skb 计算得到的数据部分的校验和 暂存到skb中 为计算完成的传输层校验和 做准备*/), //用于复制数据到skb 不同传输层由于特效不同 复制的方法也不同
		   void *from/*输出数据所在的数据块地址 它指向用户或内核空间 该参数会传递给getfrag()*/, int length/*输出数据的长度*/, int transhdrlen/*传输层首部长度*/,
		   struct ipcm_cookie *ipc/*传递到ip层的临时信息块*/, struct rtable *rt/*输出该数据的路由缓存项 在调此函数之前传输控制块已缓存路由缓存项 | 已经通过ip_route_output_flow查到了输出数据的路由缓存项*/,
		   unsigned int flags/*输出数据的标志 如MSG_MORE*/)
{ //一般用于udp套接字和raw套接字的输出接口  也用于tcp中发送ack和rst段的函数ip_send_reply
	struct inet_sock *inet = inet_sk(sk);
	struct sk_buff *skb;

	struct ip_options *opt = NULL;
	int hh_len;
	int exthdrlen; //记录IPsec中扩展首部的长度 未启用IPsec时为0
	int mtu;
	int copy;
	int err;
	int offset = 0;
	unsigned int maxfraglen, fragheaderlen;
	int csummode = CHECKSUM_NONE;

	if (flags&MSG_PROBE) //如果使用MSG_PROBE 实际并不会进行真正的数据传递 而是进行路径MTU探测
		return 0;

	if (skb_queue_empty(&sk->sk_write_queue)) { //如果传输控制块的输出队列为空 则需为传输控制块设置一些临时信息
		/*
		 * setup for corking.
		 */
		opt = ipc->opt;
		if (opt) { //如果输出数据包中存在IP选项 则将IP选项信息复制到临时信息块中 & 设置IPCORK_OPT 表示临时信息块中存在IP选项  因此设置临时信息块中的目的地址 因为在IP选项中存在源路由选项
			if (inet->cork.opt == NULL) {
				inet->cork.opt = kmalloc(sizeof(struct ip_options) + 40, sk->sk_allocation);
				if (unlikely(inet->cork.opt == NULL))
					return -ENOBUFS;
			}
			memcpy(inet->cork.opt, opt, sizeof(struct ip_options)+opt->optlen);
			inet->cork.flags |= IPCORK_OPT;
			inet->cork.addr = ipc->addr;
		}
		dst_hold(&rt->u.dst);
		inet->cork.fragsize = mtu = dst_mtu(rt->u.dst.path); //同时设置IP数据包分片大小 输出路由缓存 初始化当前发送数据包中数据长度 如果启用了IPSec则要加上IPsec首部长度
		inet->cork.rt = rt;
		inet->cork.length = 0;
		sk->sk_sndmsg_page = NULL;
		sk->sk_sndmsg_off = 0;
		if ((exthdrlen = rt->u.dst.header_len) != 0) {
			length += exthdrlen;
			transhdrlen += exthdrlen;
		}
	} else { //传输控制块的输出队列不空 则使用上次的输出路由 IP选项以及分片长度
		rt = inet->cork.rt;
		if (inet->cork.flags & IPCORK_OPT)
			opt = inet->cork.opt;

		transhdrlen = 0;
		exthdrlen = 0;
		mtu = inet->cork.fragsize;
	}
	hh_len = LL_RESERVED_SPACE(rt->u.dst.dev); //获取链路层首部 & ip首部(包括选项)的长度

	fragheaderlen = sizeof(struct iphdr) + (opt ? opt->optlen : 0);
	maxfraglen = ((mtu - fragheaderlen) & ~7) + fragheaderlen; //ip数据包的数据需要4字节对齐

	if (inet->cork.length + length > 0xFFFF - fragheaderlen) { //如果输出的数据长度超出一个ip数据包能容纳的长度 则向输出该数据包的套接字发EMGSIZE出错信息
		ip_local_error(sk, EMSGSIZE, rt->rt_dst, inet->dport, mtu-exthdrlen);
		return -EMSGSIZE;
	}

	/*
	 * transhdrlen > 0 means that this is the first fragment and we wish
	 * it won't be fragmented in the future.
	 */
	if (transhdrlen &&
	    length + fragheaderlen <= mtu &&
	    rt->u.dst.dev->features & NETIF_F_ALL_CSUM && //如果ip数据包没有分片 且输出网卡支持校验和 则设置CHECKSUM_PARTAL表示硬件执行校验和
	    !exthdrlen)
		csummode = CHECKSUM_PARTIAL;

	inet->cork.length += length;
	if (((length > mtu) && (sk->sk_protocol == IPPROTO_UDP)) && //如果输出的是UDP数据包且需要分片 同时输出网卡支持UDP分片卸载(UDP Fragmention Offload  UFO???) 则由ip_ufo_append_data进行分片处理
			(rt->u.dst.dev->features & NETIF_F_UFO)) {

		err = ip_ufo_append_data(sk, getfrag, from, length, hh_len,
					 fragheaderlen, transhdrlen, mtu,
					 flags);
		if (err)
			goto error;
		return 0;
	}

	/* So, what's going on in the loop below?
	 *
	 * We use calculated fragment length to generate chained skb,
	 * each of segments is IP fragment ready for sending to network after
	 * adding appropriate IP header.
	 */

	if ((skb = skb_peek_tail(&sk->sk_write_queue)) == NULL) //获取输出队列末尾的skb 空则分配一个新的skb用于复制数据
		goto alloc_new_skb;

	while (length > 0) { //so long 循环处理待输出数据 直到所有数据都处理完成
		/* Check if the remaining data fits into current packet. */
		copy = mtu - skb->len; //检查待发送数据是否能全部复制到最后一个skb的剩余空间中 如果可以则说明是ip分片中的上一个分片 可以不用4字节对齐
		if (copy < length) //否则需要4字节对齐 因此用8字节对齐后的mtu减去上一个skb的数据长度 得到上一个skb的剩余空间大小 也就是本次复制数据的长度
			copy = maxfraglen - skb->len; //当本次复制数据的长度copy < | = 0时 则说明上一个skb已经填满 | 空间不足8B 需要重新分配新的skb
		if (copy <= 0) {
			char *data; //如果上一个skb已经填满 | 空间不足8B | 不存在上一个skb 则将数据复制到新分配的skb中去
			unsigned int datalen;
			unsigned int fraglen;
			unsigned int fraggap;
			unsigned int alloclen;
			struct sk_buff *skb_prev;
alloc_new_skb: //如果上一个skb(通常是在调ip_append_data时 输出队列中的最后一个skb) 中存在多于8字节对齐的mtu的数据 则这些数据需移动到当前skb中 确保最后一个ip分片之外的数据能够4字节对齐 因此要计算移动到当前skb的数据长度
			skb_prev = skb;
			if (skb_prev)
				fraggap = skb_prev->len - maxfraglen;
			else
				fraggap = 0;

			/*
			 * If remaining data exceeds the mtu,
			 * we know we need more fragment(s).
			 */ // //如果剩余数据的长度超过MTU 则需更多分片
			datalen = length + fraggap; ////计算需复制到新skb中的数据长度 因为如果前一个skb还能容纳数据 则有一部分数据会复制到前一个skb中
			if (datalen > mtu - fragheaderlen)
				datalen = maxfraglen - fragheaderlen;
			fraglen = datalen + fragheaderlen; ///根据本次复制的数据长度 & ip首部长度 计算三层首部 & 其数据的总长度/

			if ((flags & MSG_MORE) && //如果后续还有数据要输出 & 网卡不支持聚合分散IO 则将MTU作为分配skb长度 是分片达到最长 为后续的数据预留空间 否则按数据的长度(包括ip首部)分配skb空间即可
			    !(rt->u.dst.dev->features&NETIF_F_SG))
				alloclen = mtu;
			else
				alloclen = datalen + fragheaderlen;

			/* The last fragment gets additional space at tail.
			 * Note, with MSG_MORE we overallocate on fragments,
			 * because we have no idea what fragment will be
			 * the last.
			 */
			if (datalen == length + fraggap)  //若是最后一个分片 & 是根据目的路由启用IPsec的情况 则可能需要多分配一些空间来支持IPsec
				alloclen += rt->u.dst.trailer_len;
			//根据是否存在传输层首部 确定用何种方法分配skb
			if (transhdrlen) { //存在传输层首部 则可以确定该分片为分片组中的第一个分片 因此在分配skb时 需考虑更多情况 如输出操作是否超时 传输层是否发生未处理的致命错误 发送通道是否已关闭 当分片不是第一个分片时 无需考虑以上情况
				skb = sock_alloc_send_skb(sk, 
						alloclen + hh_len + 15,
						(flags & MSG_DONTWAIT), &err);
			} else {
				skb = NULL;
				if (atomic_read(&sk->sk_wmem_alloc) <=
				    2 * sk->sk_sndbuf)
					skb = sock_wmalloc(sk, 
							   alloclen + hh_len + 15, 1,
							   sk->sk_allocation);
				if (unlikely(skb == NULL))
					err = -ENOBUFS;
			}
			if (skb == NULL)
				goto error;

			/*
			 *	Fill in the control structures
			 */
			skb->ip_summed = csummode; //填充用于校验的控制信息
			skb->csum = 0;
			skb_reserve(skb, hh_len); //为数据包预留用于存放二层首部 & 三层首部 & 数据空间 & 设置skb中指向三层 & 四层的指针

			/*
			 *	Find where to start putting bytes.
			 */
			data = skb_put(skb, fraglen);
			skb->nh.raw = data + exthdrlen;
			data += fragheaderlen;
			skb->h.raw = data + exthdrlen;

			if (fraggap) { //如果上一个skb的数据超过8字节对齐MTU 则将超出数据和传输层首部复制到当前skb 重新计算校验和 & 以8字节对齐MTU为长度截取上一个skb的数据
				skb->csum = skb_copy_and_csum_bits(
					skb_prev, maxfraglen,
					data + transhdrlen, fraggap, 0);
				skb_prev->csum = csum_sub(skb_prev->csum,
							  skb->csum);
				data += fraggap;
				pskb_trim_unique(skb_prev, maxfraglen);
			}

			copy = datalen - transhdrlen - fraggap; //传输层首部和上个skb多出的数据已复制 接着复制剩下的数据
			if (copy > 0 && getfrag(from, data + transhdrlen, offset, copy, fraggap, skb) < 0) {
				err = -EFAULT;
				kfree_skb(skb);
				goto error;
			}

			offset += copy; //完成本次数据复制 计算下次需要复制数据的地址 & 剩余数据长度 传输层首部已经复制 因此需要将传输层首部的transhdrlen置0 同时IPsec首部长度exthdrlen置0
			length -= datalen - fraggap;
			transhdrlen = 0;
			exthdrlen = 0;
			csummode = CHECKSUM_NONE;

			/*
			 * Put the packet on the pending queue.
			 */
			__skb_queue_tail(&sk->sk_write_queue, skb); //将复制完数据的skb添加到输出队列的尾部 接着复制剩下的数据
			continue;
		}
		//当copy > 0时 说明上一个skb有剩余空间 数据可以复制到该skb中去
		if (copy > length) //如果上个skb剩余的空间大于剩余待发送的数据长度 则剩下的数据可以一次完成
			copy = length;

		if (!(rt->u.dst.dev->features&NETIF_F_SG)) { //网卡不支持聚合分散io 则将数据复制到线性区域的剩余空间
			unsigned int off;

			off = skb->len;
			if (getfrag(from, skb_put(skb, copy), 
					offset, copy, off, skb) < 0) {
				__skb_trim(skb, off);
				err = -EFAULT;
				goto error;
			}
		} else { //网卡支持聚合分散io 则将数据复制到聚合分散io区域的空间
			int i = skb_shinfo(skb)->nr_frags; //获取分片数组中最后一个分片指向的页面 & 已使用数据在分片的页内偏移
			skb_frag_t *frag = &skb_shinfo(skb)->frags[i-1];
			struct page *page = sk->sk_sndmsg_page;
			int off = sk->sk_sndmsg_off;
			unsigned int left;

			if (page && (left = PAGE_SIZE - off) > 0) { //如果缓存页面存在 & 有剩余空间 则先使用缓存页面 将数据复制到缓存页面
				if (copy >= left) //如果待复制数据大于页面中剩余空间 则根据页面剩余空间重新设定本次复制数据长度 确保待复制数据长度不超过页面中剩余空间长度
					copy = left;
				if (page != frag->page) { //如果传输控制块的缓存页不是最后一个聚合分散io页面 则直接使用该页面 将其添加到聚合分散io页面数组中 并确定将数据复制到的页面
					if (i == MAX_SKB_FRAGS) {
						err = -EMSGSIZE;
						goto error;
					}
					get_page(page);
	 				skb_fill_page_desc(skb, i, page, sk->sk_sndmsg_off, 0);
					frag = &skb_shinfo(skb)->frags[i];
				}
			} else if (i < MAX_SKB_FRAGS) { //如果缓存页面不存在或页面没有剩余空间 & 传输控制块的聚合分散io页面数量到达上限 则添加新的分片 & 分配新的页面
				if (copy > PAGE_SIZE) //如果待复制数据大于页面的长度 则根据页面长度重新设定本次复制数据的长度 确保待复制的数据长度不超过页面长度
					copy = PAGE_SIZE;
				page = alloc_pages(sk->sk_allocation, 0); //分配页面 & 安装到skb的聚合分散io页面数组中 确定将数据复制到该页面 同时刷新传输控制块中指向的缓存页面 更新传输控制块发送使用的缓存大小
				if (page == NULL)  {
					err = -ENOMEM;
					goto error;
				}
				sk->sk_sndmsg_page = page;
				sk->sk_sndmsg_off = 0;

				skb_fill_page_desc(skb, i, page, 0, 0);
				frag = &skb_shinfo(skb)->frags[i];
				skb->truesize += PAGE_SIZE;
				atomic_add(PAGE_SIZE, &sk->sk_wmem_alloc);
			} else { //如果缓存页面不存在 | 页面没有剩余空间 & 传输控制块的聚合分散io缓存块数到达上限 说明待发送的数据太长 已经超过ip数据包的最大长度
				err = -EMSGSIZE;
				goto error;
			}
			if (getfrag(from, page_address(frag->page)+frag->page_offset+frag->size, offset, copy, skb->len, skb) < 0) {
				err = -EFAULT;
				goto error;
			}
			sk->sk_sndmsg_off += copy; //复制完数据后 更新数据尾端在最后一个分片页内的偏移 & 分片页面中已使用的长度 skb的数据部分长度 分片中数据的长度
			frag->size += copy;
			skb->len += copy;
			skb->data_len += copy;
		}
		offset += copy; //完成本次复制数据 计算下次需要复制数据的地址 & 剩余数据长度
		length -= copy;
	}

	return 0;

error:
	inet->cork.length -= length;
	IP_INC_STATS(IPSTATS_MIB_OUTDISCARDS);
	return err; 
}

ssize_t	ip_append_page(struct sock *sk, struct page *page,
		       int offset, size_t size, int flags)
{
	struct inet_sock *inet = inet_sk(sk);
	struct sk_buff *skb;
	struct rtable *rt;
	struct ip_options *opt = NULL;
	int hh_len;
	int mtu;
	int len;
	int err;
	unsigned int maxfraglen, fragheaderlen, fraggap;

	if (inet->hdrincl)
		return -EPERM;

	if (flags&MSG_PROBE)
		return 0;

	if (skb_queue_empty(&sk->sk_write_queue))
		return -EINVAL;

	rt = inet->cork.rt;
	if (inet->cork.flags & IPCORK_OPT)
		opt = inet->cork.opt;

	if (!(rt->u.dst.dev->features&NETIF_F_SG))
		return -EOPNOTSUPP;

	hh_len = LL_RESERVED_SPACE(rt->u.dst.dev);
	mtu = inet->cork.fragsize;

	fragheaderlen = sizeof(struct iphdr) + (opt ? opt->optlen : 0);
	maxfraglen = ((mtu - fragheaderlen) & ~7) + fragheaderlen;

	if (inet->cork.length + size > 0xFFFF - fragheaderlen) {
		ip_local_error(sk, EMSGSIZE, rt->rt_dst, inet->dport, mtu);
		return -EMSGSIZE;
	}

	if ((skb = skb_peek_tail(&sk->sk_write_queue)) == NULL)
		return -EINVAL;

	inet->cork.length += size;
	if ((sk->sk_protocol == IPPROTO_UDP) &&
	    (rt->u.dst.dev->features & NETIF_F_UFO)) {
		skb_shinfo(skb)->gso_size = mtu - fragheaderlen;
		skb_shinfo(skb)->gso_type = SKB_GSO_UDP;
	}


	while (size > 0) {
		int i;

		if (skb_is_gso(skb))
			len = size;
		else {

			/* Check if the remaining data fits into current packet. */
			len = mtu - skb->len;
			if (len < size)
				len = maxfraglen - skb->len;
		}
		if (len <= 0) {
			struct sk_buff *skb_prev;
			char *data;
			struct iphdr *iph;
			int alloclen;

			skb_prev = skb;
			fraggap = skb_prev->len - maxfraglen;

			alloclen = fragheaderlen + hh_len + fraggap + 15;
			skb = sock_wmalloc(sk, alloclen, 1, sk->sk_allocation);
			if (unlikely(!skb)) {
				err = -ENOBUFS;
				goto error;
			}

			/*
			 *	Fill in the control structures
			 */
			skb->ip_summed = CHECKSUM_NONE;
			skb->csum = 0;
			skb_reserve(skb, hh_len);

			/*
			 *	Find where to start putting bytes.
			 */
			data = skb_put(skb, fragheaderlen + fraggap);
			skb->nh.iph = iph = (struct iphdr *)data;
			data += fragheaderlen;
			skb->h.raw = data;

			if (fraggap) {
				skb->csum = skb_copy_and_csum_bits(
					skb_prev, maxfraglen,
					data, fraggap, 0);
				skb_prev->csum = csum_sub(skb_prev->csum,
							  skb->csum);
				pskb_trim_unique(skb_prev, maxfraglen);
			}

			/*
			 * Put the packet on the pending queue.
			 */
			__skb_queue_tail(&sk->sk_write_queue, skb);
			continue;
		}

		i = skb_shinfo(skb)->nr_frags;
		if (len > size)
			len = size;
		if (skb_can_coalesce(skb, i, page, offset)) {
			skb_shinfo(skb)->frags[i-1].size += len;
		} else if (i < MAX_SKB_FRAGS) {
			get_page(page);
			skb_fill_page_desc(skb, i, page, offset, len);
		} else {
			err = -EMSGSIZE;
			goto error;
		}

		if (skb->ip_summed == CHECKSUM_NONE) {
			__wsum csum;
			csum = csum_page(page, offset, len);
			skb->csum = csum_block_add(skb->csum, csum, skb->len);
		}

		skb->len += len;
		skb->data_len += len;
		offset += len;
		size -= len;
	}
	return 0;

error:
	inet->cork.length -= size;
	IP_INC_STATS(IPSTATS_MIB_OUTDISCARDS);
	return err;
}

/*
 *	Combined all pending IP fragments on the socket as one IP datagram
 *	and push them out.
 */
int ip_push_pending_frames(struct sock *sk) //将输出队列上的多个分片合成一个完整的ip数据包 通过ip_output输出
{
	struct sk_buff *skb, *tmp_skb;
	struct sk_buff **tail_skb;
	struct inet_sock *inet = inet_sk(sk);
	struct ip_options *opt = NULL;
	struct rtable *rt = inet->cork.rt;
	struct iphdr *iph;
	__be16 df = 0;
	__u8 ttl;
	int err = 0;

	if ((skb = __skb_dequeue(&sk->sk_write_queue)) == NULL) //out_list is null
		goto out;
	tail_skb = &(skb_shinfo(skb)->frag_list); //获取输出队列中fraglist链表 用于存放处理后的分片

	/* move skb->data to ip header from ext header */
	if (skb->data < skb->nh.raw) //如果skb的data指针位置不准 调整到ip首部处 因为接着处理的是ip数据包 需要填充ip首部
		__skb_pull(skb, skb->nh.raw - skb->data);
	while ((tmp_skb = __skb_dequeue(&sk->sk_write_queue)) != NULL) { //去除后续skb中的ip首部后 链接到第一个skb的fraglist上 组成一个分片 为后续的分片做准备
		__skb_pull(tmp_skb, skb->h.raw - skb->nh.raw);
		*tail_skb = tmp_skb;
		tail_skb = &(tmp_skb->next);
		skb->len += tmp_skb->len;
		skb->data_len += tmp_skb->len;
		skb->truesize += tmp_skb->truesize;
		__sock_put(tmp_skb->sk);
		tmp_skb->destructor = NULL;
		tmp_skb->sk = NULL;
	}

	/* Unless user demanded real pmtu discovery (IP_PMTUDISC_DO), we allow
	 * to fragment the frame generated here. No matter, what transforms
	 * how transforms change size of the packet, it will come out.
	 */
	if (inet->pmtudisc != IP_PMTUDISC_DO) //在不启用路径mtu发现功能 | 输出数据包长度小于mtu & 本传输控制块输出的ip数据包不能分片 则给ip首部添加df
		skb->local_df = 1;

	/* DF bit is set when we want to see DF on outgoing frames.
	 * If local_df is set too, we still allow to fragment this frame
	 * locally. */
	if (inet->pmtudisc == IP_PMTUDISC_DO ||
	    (skb->len <= dst_mtu(&rt->u.dst) &&
	     ip_dont_fragment(sk, &rt->u.dst)))
		df = htons(IP_DF);

	if (inet->cork.flags & IPCORK_OPT) //如果ip选项信息已保存到传输控制块中 则获取ip选项信息指针 准备用于构建ip首部中的选项
		opt = inet->cork.opt;

	if (rt->rt_type == RTN_MULTICAST)
		ttl = inet->mc_ttl;
	else
		ttl = ip_select_ttl(inet, &rt->u.dst); //获取生存时间 用于设置到待输出的ip首部中

	iph = (struct iphdr *)skb->data; //构建ip首部 设置ip首部中各字段 包括ip选项
	iph->version = 4;
	iph->ihl = 5;
	if (opt) {
		iph->ihl += opt->optlen>>2;
		ip_options_build(skb, opt, inet->cork.addr, rt, 0); //设置输出数据包的优先级 & 目的路由
	}
	iph->tos = inet->tos;
	iph->tot_len = htons(skb->len);
	iph->frag_off = df;
	ip_select_ident(iph, &rt->u.dst, sk);
	iph->ttl = ttl;
	iph->protocol = sk->sk_protocol;
	iph->saddr = rt->rt_src;
	iph->daddr = rt->rt_dst;
	ip_send_check(iph);

	skb->priority = sk->sk_priority;
	skb->dst = dst_clone(&rt->u.dst);

	/* Netfilter gets whole the not fragmented skb. */
	err = NF_HOOK(PF_INET, NF_IP_LOCAL_OUT, skb, NULL,  //通过NF_IP_LOCAL_OUT的netfilter处理后 由dst_output输出数据包
		      skb->dst->dev, dst_output);
	if (err) {
		if (err > 0)
			err = inet->recverr ? net_xmit_errno(err) : 0;
		if (err)
			goto error;
	}

out:
	inet->cork.flags &= ~IPCORK_OPT; //无论是否成功输出ip数据包 完成后都要删除保存到传输控制块中的ip选项信息
	kfree(inet->cork.opt);
	inet->cork.opt = NULL;
	if (inet->cork.rt) {
		ip_rt_put(inet->cork.rt);
		inet->cork.rt = NULL;
	}
	return err;

error:
	IP_INC_STATS(IPSTATS_MIB_OUTDISCARDS); //处理输出数据包发生错误的情况
	goto out;
}

/*
 *	Throw away all pending data on the socket.
 */
void ip_flush_pending_frames(struct sock *sk)
{
	struct inet_sock *inet = inet_sk(sk);
	struct sk_buff *skb;

	while ((skb = __skb_dequeue_tail(&sk->sk_write_queue)) != NULL)
		kfree_skb(skb);

	inet->cork.flags &= ~IPCORK_OPT;
	kfree(inet->cork.opt);
	inet->cork.opt = NULL;
	if (inet->cork.rt) {
		ip_rt_put(inet->cork.rt);
		inet->cork.rt = NULL;
	}
}


/*
 *	Fetch data from kernel space and fill in checksum if needed.
 */
static int ip_reply_glue_bits(void *dptr, char *to, int offset, 
			      int len, int odd, struct sk_buff *skb)
{
	__wsum csum;

	csum = csum_partial_copy_nocheck(dptr+offset, to, len, 0);
	skb->csum = csum_block_add(skb->csum, csum, odd);
	return 0;  
}

/* 
 *	Generic function to send a packet as reply to another packet.
 *	Used to send TCP resets so far. ICMP should use this function too.
 *
 *	Should run single threaded per socket because it uses the sock 
 *     	structure to pass arguments.
 *
 *	LATER: switch from ip_build_xmit to ip_append_*
 */
void ip_send_reply(struct sock *sk/*输出tcp段的传输控制块*/, struct sk_buff *skb/*对方发送过来的tcp段*/, struct ip_reply_arg *arg, //用于构成 & 输出rst和ack段 在tcp_v4_send_reset和tcp_v4_send_ack(connect 最后一个ack)中调用
		   unsigned int len)                                                                         //传递给ip_send_reply的一些参数集合: 包括输出的数据 tcp伪首部校验和 tcp首部中校验和字段在首部中的偏移
{
	struct inet_sock *inet = inet_sk(sk);
	struct {
		struct ip_options	opt;
		char			data[40];
	} replyopts;
	struct ipcm_cookie ipc;
	__be32 daddr;
	struct rtable *rt = (struct rtable*)skb->dst;

	if (ip_options_echo(&replyopts.opt, skb)) //从待输出的ip数据包中得到选项 用于处理源路由选项
		return;

	daddr = ipc.addr = rt->rt_src;
	ipc.opt = NULL;

	if (replyopts.opt.optlen) { //根据对端发来的数据包的输入路由 获取对方的ip地址
		ipc.opt = &replyopts.opt;

		if (ipc.opt->srr) //如果输入的ip数据包启用了源路由选项 则将下一跳的ip地址作为目的ip
			daddr = replyopts.opt.faddr;
	}

	{
		struct flowi fl = { .nl_u = { .ip4_u = //根据目的ip 源ip等查找输出到对方的路由 如果命中则可以输出数据包 否则终止输出
					      { .daddr = daddr,
						.saddr = rt->rt_spec_dst,
						.tos = RT_TOS(skb->nh.iph->tos) } },
				    /* Not quite clean, but right. */
				    .uli_u = { .ports =
					       { .sport = skb->h.th->dest,
					         .dport = skb->h.th->source } },
				    .proto = sk->sk_protocol };
		security_skb_classify_flow(skb, &fl);
		if (ip_route_output_key(&rt, &fl))
			return;
	}

	/* And let IP do all the hard work.

	   This chunk is not reenterable, hence spinlock.
	   Note that it uses the fact, that this function is called
	   with locally disabled BH and that sk cannot be already spinlocked.
	 */
	bh_lock_sock(sk);
	inet->tos = skb->nh.iph->tos; //根据输入的skb更新一些属性到传输控制块中 如TOS 优先级等
	sk->sk_priority = skb->priority;
	sk->sk_protocol = skb->nh.iph->protocol;
	ip_append_data(sk, ip_reply_glue_bits, arg->iov->iov_base, len, 0, //先将数据添加到输出队列末尾的skb中 或将数据复制到新生成的skb中并添加到输出队列中 然后 如果输出队列非空 则计算第一个skb的传输层校验和 & 将其发送出去
		       &ipc, rt, MSG_DONTWAIT);
	if ((skb = skb_peek(&sk->sk_write_queue)) != NULL) {
		if (arg->csumoffset >= 0)
			*((__sum16 *)skb->h.raw + arg->csumoffset) = csum_fold(csum_add(skb->csum, arg->csum));
		skb->ip_summed = CHECKSUM_NONE;
		ip_push_pending_frames(sk);
	}

	bh_unlock_sock(sk);

	ip_rt_put(rt);
}

void __init ip_init(void) //初始化ip层: 初始化路由模块 对端信息管理模块 组播proc文件注册
{
	ip_rt_init();
	inet_initpeers();

#if defined(CONFIG_IP_MULTICAST) && defined(CONFIG_PROC_FS)
	igmp_mc_proc_init();
#endif
}

EXPORT_SYMBOL(ip_generic_getfrag);
EXPORT_SYMBOL(ip_queue_xmit);
EXPORT_SYMBOL(ip_send_check);

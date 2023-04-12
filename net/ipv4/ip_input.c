/*
 * INET		An implementation of the TCP/IP protocol suite for the LINUX
 *		operating system.  INET is implemented using the  BSD Socket
 *		interface as the means of communication with the user level.
 *
 *		The Internet Protocol (IP) module.
 *
 * Version:	$Id: ip_input.c,v 1.55 2002/01/12 07:39:45 davem Exp $
 *
 * Authors:	Ross Biro
 *		Fred N. van Kempen, <waltje@uWalt.NL.Mugnet.ORG>
 *		Donald Becker, <becker@super.org>
 *		Alan Cox, <Alan.Cox@linux.org>
 *		Richard Underwood
 *		Stefan Becker, <stefanb@yello.ping.de>
 *		Jorge Cwik, <jorge@laser.satlink.net>
 *		Arnt Gulbrandsen, <agulbra@nvg.unit.no>
 *		
 *
 * Fixes:
 *		Alan Cox	:	Commented a couple of minor bits of surplus code
 *		Alan Cox	:	Undefining IP_FORWARD doesn't include the code
 *					(just stops a compiler warning).
 *		Alan Cox	:	Frames with >=MAX_ROUTE record routes, strict routes or loose routes
 *					are junked rather than corrupting things.
 *		Alan Cox	:	Frames to bad broadcast subnets are dumped
 *					We used to process them non broadcast and
 *					boy could that cause havoc.
 *		Alan Cox	:	ip_forward sets the free flag on the
 *					new frame it queues. Still crap because
 *					it copies the frame but at least it
 *					doesn't eat memory too.
 *		Alan Cox	:	Generic queue code and memory fixes.
 *		Fred Van Kempen :	IP fragment support (borrowed from NET2E)
 *		Gerhard Koerting:	Forward fragmented frames correctly.
 *		Gerhard Koerting: 	Fixes to my fix of the above 8-).
 *		Gerhard Koerting:	IP interface addressing fix.
 *		Linus Torvalds	:	More robustness checks
 *		Alan Cox	:	Even more checks: Still not as robust as it ought to be
 *		Alan Cox	:	Save IP header pointer for later
 *		Alan Cox	:	ip option setting
 *		Alan Cox	:	Use ip_tos/ip_ttl settings
 *		Alan Cox	:	Fragmentation bogosity removed
 *					(Thanks to Mark.Bush@prg.ox.ac.uk)
 *		Dmitry Gorodchanin :	Send of a raw packet crash fix.
 *		Alan Cox	:	Silly ip bug when an overlength
 *					fragment turns up. Now frees the
 *					queue.
 *		Linus Torvalds/ :	Memory leakage on fragmentation
 *		Alan Cox	:	handling.
 *		Gerhard Koerting:	Forwarding uses IP priority hints
 *		Teemu Rantanen	:	Fragment problems.
 *		Alan Cox	:	General cleanup, comments and reformat
 *		Alan Cox	:	SNMP statistics
 *		Alan Cox	:	BSD address rule semantics. Also see
 *					UDP as there is a nasty checksum issue
 *					if you do things the wrong way.
 *		Alan Cox	:	Always defrag, moved IP_FORWARD to the config.in file
 *		Alan Cox	: 	IP options adjust sk->priority.
 *		Pedro Roque	:	Fix mtu/length error in ip_forward.
 *		Alan Cox	:	Avoid ip_chk_addr when possible.
 *	Richard Underwood	:	IP multicasting.
 *		Alan Cox	:	Cleaned up multicast handlers.
 *		Alan Cox	:	RAW sockets demultiplex in the BSD style.
 *		Gunther Mayer	:	Fix the SNMP reporting typo
 *		Alan Cox	:	Always in group 224.0.0.1
 *	Pauline Middelink	:	Fast ip_checksum update when forwarding
 *					Masquerading support.
 *		Alan Cox	:	Multicast loopback error for 224.0.0.1
 *		Alan Cox	:	IP_MULTICAST_LOOP option.
 *		Alan Cox	:	Use notifiers.
 *		Bjorn Ekwall	:	Removed ip_csum (from slhc.c too)
 *		Bjorn Ekwall	:	Moved ip_fast_csum to ip.h (inline!)
 *		Stefan Becker   :       Send out ICMP HOST REDIRECT
 *	Arnt Gulbrandsen	:	ip_build_xmit
 *		Alan Cox	:	Per socket routing cache
 *		Alan Cox	:	Fixed routing cache, added header cache.
 *		Alan Cox	:	Loopback didn't work right in original ip_build_xmit - fixed it.
 *		Alan Cox	:	Only send ICMP_REDIRECT if src/dest are the same net.
 *		Alan Cox	:	Incoming IP option handling.
 *		Alan Cox	:	Set saddr on raw output frames as per BSD.
 *		Alan Cox	:	Stopped broadcast source route explosions.
 *		Alan Cox	:	Can disable source routing
 *		Takeshi Sone    :	Masquerading didn't work.
 *	Dave Bonn,Alan Cox	:	Faster IP forwarding whenever possible.
 *		Alan Cox	:	Memory leaks, tramples, misc debugging.
 *		Alan Cox	:	Fixed multicast (by popular demand 8))
 *		Alan Cox	:	Fixed forwarding (by even more popular demand 8))
 *		Alan Cox	:	Fixed SNMP statistics [I think]
 *	Gerhard Koerting	:	IP fragmentation forwarding fix
 *		Alan Cox	:	Device lock against page fault.
 *		Alan Cox	:	IP_HDRINCL facility.
 *	Werner Almesberger	:	Zero fragment bug
 *		Alan Cox	:	RAW IP frame length bug
 *		Alan Cox	:	Outgoing firewall on build_xmit
 *		A.N.Kuznetsov	:	IP_OPTIONS support throughout the kernel
 *		Alan Cox	:	Multicast routing hooks
 *		Jos Vos		:	Do accounting *before* call_in_firewall
 *	Willy Konynenberg	:	Transparent proxying support
 *
 *  
 *
 * To Fix:
 *		IP fragmentation wants rewriting cleanly. The RFC815 algorithm is much more efficient
 *		and could be made very efficient with the addition of some virtual memory hacks to permit
 *		the allocation of a buffer that can then be 'grown' by twiddling page tables.
 *		Output fragmentation wants updating along with the buffer management to use a single 
 *		interleaved copy algorithm so that fragmenting has a one copy overhead. Actual packet
 *		output should probably do its own fragmentation at the UDP/RAW layer. TCP shouldn't cause
 *		fragmentation anyway.
 *
 *		This program is free software; you can redistribute it and/or
 *		modify it under the terms of the GNU General Public License
 *		as published by the Free Software Foundation; either version
 *		2 of the License, or (at your option) any later version.
 */

#include <asm/system.h>
#include <linux/module.h>
#include <linux/types.h>
#include <linux/kernel.h>
#include <linux/string.h>
#include <linux/errno.h>

#include <linux/net.h>
#include <linux/socket.h>
#include <linux/sockios.h>
#include <linux/in.h>
#include <linux/inet.h>
#include <linux/inetdevice.h>
#include <linux/netdevice.h>
#include <linux/etherdevice.h>

#include <net/snmp.h>
#include <net/ip.h>
#include <net/protocol.h>
#include <net/route.h>
#include <linux/skbuff.h>
#include <net/sock.h>
#include <net/arp.h>
#include <net/icmp.h>
#include <net/raw.h>
#include <net/checksum.h>
#include <linux/netfilter_ipv4.h>
#include <net/xfrm.h>
#include <linux/mroute.h>
#include <linux/netlink.h>

/*
 *	SNMP management statistics
 */

DEFINE_SNMP_STAT(struct ipstats_mib, ip_statistics) __read_mostly;

/*
 *	Process Router Attention IP option
 */ 
int ip_call_ra_chain(struct sk_buff *skb)
{
	struct ip_ra_chain *ra;
	u8 protocol = skb->nh.iph->protocol;
	struct sock *last = NULL;

	read_lock(&ip_ra_lock);
	for (ra = ip_ra_chain; ra; ra = ra->next) {
		struct sock *sk = ra->sk;

		/* If socket is bound to an interface, only report
		 * the packet if it came  from that interface.
		 */
		if (sk && inet_sk(sk)->num == protocol &&
		    (!sk->sk_bound_dev_if ||
		     sk->sk_bound_dev_if == skb->dev->ifindex)) {
			if (skb->nh.iph->frag_off & htons(IP_MF|IP_OFFSET)) {
				skb = ip_defrag(skb, IP_DEFRAG_CALL_RA_CHAIN);
				if (skb == NULL) {
					read_unlock(&ip_ra_lock);
					return 1;
				}
			}
			if (last) {
				struct sk_buff *skb2 = skb_clone(skb, GFP_ATOMIC);
				if (skb2)
					raw_rcv(last, skb2);
			}
			last = sk;
		}
	}

	if (last) {
		raw_rcv(last, skb);
		read_unlock(&ip_ra_lock);
		return 1;
	}
	read_unlock(&ip_ra_lock);
	return 0;
}

static inline int ip_local_deliver_finish(struct sk_buff *skb) //发给我的完整ip数据包 //网络层--->传输层
{
	int ihl = skb->nh.iph->ihl*4;

	__skb_pull(skb, ihl); //在ip数据包传递给传输层之前 去掉ip头

        /* Point into the IP datagram, just past the header. */
        skb->h.raw = skb->data;

	rcu_read_lock();
	{
		/* Note: See raw.c and net/raw.h, RAWV4_HTABLE_SIZE==MAX_INET_PROTOS */
		int protocol = skb->nh.iph->protocol;
		int hash;
		struct sock *raw_sk;
		struct net_protocol *ipprot;

	resubmit:
		hash = protocol & (MAX_INET_PROTOS - 1);
		raw_sk = sk_head(&raw_v4_htable[hash]);

		/* If there maybe a raw socket we must check - if not we
		 * don't care less
		 */
		if (raw_sk && !raw_v4_input(skb, skb->nh.iph, hash)) //如果是raw套接字接收数据包则需复制一份 输入到接收该数据包的套接字
			raw_sk = NULL;     //根据传输层协议号得到hash 查raw_v4_htable散列表中 以该值为关键字的hash桶是否空 如果不空 则说明创建了raw套接字 复制该数据包到注册到该桶中的所有套接字

		if ((ipprot = rcu_dereference(inet_protos[hash])) != NULL) { //查找上层协议
			int ret;

			if (!ipprot->no_policy) {
				if (!xfrm4_policy_check(NULL, XFRM_POLICY_IN, skb)) {
					kfree_skb(skb);
					goto out;
				}
				nf_reset(skb);
			}
			ret = ipprot->handler(skb); //传输层接收回调: tcp_v4_recv udp_rcv icmp_rcv igmp_rcv
			if (ret < 0) {
				protocol = -ret;
				goto resubmit;
			}
			IP_INC_STATS_BH(IPSTATS_MIB_INDELIVERS);
		} else { //无相应的传输层协议 丢弃
			if (!raw_sk) {
				if (xfrm4_policy_check(NULL, XFRM_POLICY_IN, skb)) {
					IP_INC_STATS_BH(IPSTATS_MIB_INUNKNOWNPROTOS);
					icmp_send(skb, ICMP_DEST_UNREACH,
						  ICMP_PROT_UNREACH, 0);
				}
			} else
				IP_INC_STATS_BH(IPSTATS_MIB_INDELIVERS);
			kfree_skb(skb);
		}
	}
 out:
	rcu_read_unlock();

	return 0;
}

/*
 * 	Deliver IP Packets to the higher protocol layers.
 */ 
int ip_local_deliver(struct sk_buff *skb)                           // 已经确定是发给我的 先判断接收到的数据包是不是分片 若分片则将分片重组 若不是分片或分片重组得到完整ip数据包 则本地输入点通过
{
	/*
	 *	Reassemble IP fragments.
	 */

	if (skb->nh.iph->frag_off & htons(IP_MF|IP_OFFSET)) {
		skb = ip_defrag(skb, IP_DEFRAG_LOCAL_DELIVER);              // ip数据包分片重组
		if (!skb)                                                   // ip数据包分片未重组完成 完成则返回ip数据包skb头指针
			return 0;
	}

	return NF_HOOK(PF_INET, NF_IP_LOCAL_IN, skb, skb->dev, NULL,    // netfilter处理后调 ip_local_deliver_finish完成数据包的本地输入
		       ip_local_deliver_finish);
}

// http://blog.chinaunix.net/uid-23207633-id-292140.html
static inline int ip_rcv_options(struct sk_buff *skb)               // 在输入时 解析IP首部中的选项 保存到inet_skb_parm结构的opt成员中 在输出时 ip_options_build根据inet_skb_parm结构的opt成员将其反应到IP头中 在转发时 ip_forward_options根据选项做适当处理
{
	struct ip_options *opt;
	struct iphdr *iph;
	struct net_device *dev = skb->dev;

	/* It looks as overkill, because not all
	   IP options require packet mangling.
	   But it is the easiest for now, especially taking
	   into account that combination of IP options
	   and running sniffer is extremely rare condition.
					      --ANK (980813)
	*/
	if (skb_cow(skb, skb_headroom(skb))) {                          // 确保数据包足够的头部空间
		IP_INC_STATS_BH(IPSTATS_MIB_INDISCARDS);
		goto drop;
	}

	iph = skb->nh.iph;

	if (ip_options_compile(NULL, skb)) {                            // 调ip_options_compile解析skb中的nh.raw指向的ip首部中ip选项 到 skb的cb中 ip层的私有数据cb为一个ip选项信息块
		IP_INC_STATS_BH(IPSTATS_MIB_INHDRERRORS);
		goto drop;
	}

	opt = &(IPCB(skb)->opt);                                        // 如果存在源路由选项&系统允许接收带源路由选项的ip数据包 则接收并处理ip数据包的源路由选项 否则丢弃
	if (unlikely(opt->srr)) {
		struct in_device *in_dev = in_dev_get(dev);
		if (in_dev) {
			if (!IN_DEV_SOURCE_ROUTE(in_dev)) {
				if (IN_DEV_LOG_MARTIANS(in_dev) &&
				    net_ratelimit())
					printk(KERN_INFO "source route option "
					       "%u.%u.%u.%u -> %u.%u.%u.%u\n",
					       NIPQUAD(iph->saddr),
					       NIPQUAD(iph->daddr));
				in_dev_put(in_dev);
				goto drop;
			}

			in_dev_put(in_dev);
		}

		if (ip_options_rcv_srr(skb))
			goto drop;
	}

	return 0;
drop:
	return -1;
}

static inline int ip_rcv_finish(struct sk_buff *skb)                    // 在ip_rcv中当ip数据经过netfilter pre-route模块后被调用 主要功能是: 如果还没有为该数据包查找输入路由缓存 则调ip_route_input为其查找输入路由缓存
{                                                                       // 接着处理ip数据包首部中的选项 最后根据输入路由缓存输入到本地或转发 本机则调ip_local_deliver 转发则调ip_forward
	struct iphdr *iph = skb->nh.iph;

	/*
	 *	Initialise the virtual path cache for the packet. It describes
	 *	how the packet travels inside Linux networking.
	 */ 
	if (skb->dst == NULL) {
		int err = ip_route_input(skb, iph->daddr, iph->saddr, iph->tos,
					 skb->dev);
		if (unlikely(err)) {                                            // 查询路由失败则丢弃报文
			if (err == -EHOSTUNREACH)
				IP_INC_STATS_BH(IPSTATS_MIB_INADDRERRORS);
			goto drop; 
		}
	}

#ifdef CONFIG_NET_CLS_ROUTE
	if (unlikely(skb->dst->tclassid)) {
		struct ip_rt_acct *st = ip_rt_acct + 256*smp_processor_id();
		u32 idx = skb->dst->tclassid;
		st[idx&0xFF].o_packets++;
		st[idx&0xFF].o_bytes+=skb->len;
		st[(idx>>16)&0xFF].i_packets++;
		st[(idx>>16)&0xFF].i_bytes+=skb->len;
	}
#endif

	if (iph->ihl > 5 && ip_rcv_options(skb))                            // 判断ip头是否存在选项 有则调ip_rcv_optinos 处理选项
		goto drop;

	return dst_input(skb);                                              // 根据输入路由缓存决定输入本地(ip_local_deliver)或转发(ip_forward)

drop:
        kfree_skb(skb);
        return NET_RX_DROP;
}

/*
 * 	Main IP Receive routine.
 */ 
int ip_rcv(struct sk_buff *skb, struct net_device *dev, struct packet_type *pt, struct net_device *orig_dev) 
                                                                                        // 当网卡收到报文时 会根据网络层协议号从ptype_base散列表中找到对应的接收函数
{                                                                                       // ipv4数据报类型为ip_packet_type 是在网络初始化时 通过dev_add_pack注册到系统中的ptype_base散列中的 对应的接收函数为ip_rcv // core/dev.c
	struct iphdr *iph;                                                                  // ip_rcv处理完数据报 并经pre-routing点netfilter处理后 再由ip_rcv_finish处理 里面根据数据报的路由信息 决定这个数据报是转发还是输入到本机
	u32 len;                                                                            // 本机则调ip_local_deliver 转发则调ip_forward

	/* When the interface is in promisc. mode, drop all the crap
	 * that it receives, do not try to analyse it.
	 */
	if (skb->pkt_type == PACKET_OTHERHOST)                                              // 丢弃不去往本地的数据包 此处只接收发往本机的数据包
		goto drop;

	IP_INC_STATS_BH(IPSTATS_MIB_INRECEIVES);

	if ((skb = skb_share_check(skb, GFP_ATOMIC)) == NULL) {                             // 检测数据包是否为共享数据包 是则复制副本 因为处理过程中可能修改数据包中的信息
		IP_INC_STATS_BH(IPSTATS_MIB_INDISCARDS);
		goto out;
	}

	if (!pskb_may_pull(skb, sizeof(struct iphdr)))                                      // 通过判断数据包长度检测数据包是否有效 不能小于ip首部长度
		goto inhdr_error;

	iph = skb->nh.iph;

	/*
	 *	RFC1122: 3.1.2.2 MUST silently discard any IP frame that fails the checksum.
	 *
	 *	Is the datagram acceptable?
	 *
	 *	1.	Length at least the size of an ip header
	 *	2.	Version of 4
	 *	3.	Checksums correctly. [Speed optimisation for later, skip loopback checksums]
	 *	4.	Doesn't have a bogus length
	 */

	if (iph->ihl < 5 || iph->version != 4) //20B  ipv4
		goto inhdr_error;

	if (!pskb_may_pull(skb, iph->ihl*4))
		goto inhdr_error;

	iph = skb->nh.iph;

	if (unlikely(ip_fast_csum((u8 *)iph, iph->ihl)))                                    // check sum
		goto inhdr_error;

	len = ntohs(iph->tot_len);
	if (skb->len < len || len < (iph->ihl*4))                                           // 根据ip头中的数据包总长度值检测数据包是否有效
		goto inhdr_error;

	/* Our transport medium may have padded the buffer out. Now we know it
	 * is IP we can trim to the true length of the frame.
	 * Note this now means skb->len holds ntohs(iph->tot_len).
	 */
	if (pskb_trim_rcsum(skb, len)) {                                                    // 根据ip头中的数据包总长度重新设置skb长度--->有点http cl的味道
		IP_INC_STATS_BH(IPSTATS_MIB_INDISCARDS);
		goto drop;
	}

	/* Remove any debris in the socket control block */
	memset(IPCB(skb), 0, sizeof(struct inet_skb_parm));                                 // 将skb中的ip控制块清零 以便后续对ip选项的处理

	return NF_HOOK(PF_INET, NF_IP_PRE_ROUTING, skb, dev, NULL,                          // 通过netfilter模块处理后 调ip_rcv_finish完成ip报输入
		       ip_rcv_finish);

inhdr_error:                                                                            // 处理无效报文
	IP_INC_STATS_BH(IPSTATS_MIB_INHDRERRORS);
drop:
        kfree_skb(skb);
out:
        return NET_RX_DROP;
}

EXPORT_SYMBOL(ip_statistics);

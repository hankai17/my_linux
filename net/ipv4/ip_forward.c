/*
 * INET		An implementation of the TCP/IP protocol suite for the LINUX
 *		operating system.  INET is implemented using the  BSD Socket
 *		interface as the means of communication with the user level.
 *
 *		The IP forwarding functionality.
 *		
 * Version:	$Id: ip_forward.c,v 1.48 2000/12/13 18:31:48 davem Exp $
 *
 * Authors:	see ip.c
 *
 * Fixes:
 *		Many		:	Split from ip.c , see ip_input.c for 
 *					history.
 *		Dave Gregorich	:	NULL ip_rt_put fix for multicast 
 *					routing.
 *		Jos Vos		:	Add call_out_firewall before sending,
 *					use output device for accounting.
 *		Jos Vos		:	Call forward firewall after routing
 *					(always use output device).
 *		Mike McLagan	:	Routing by source
 */

#include <linux/types.h>
#include <linux/mm.h>
#include <linux/sched.h>
#include <linux/skbuff.h>
#include <linux/ip.h>
#include <linux/icmp.h>
#include <linux/netdevice.h>
#include <net/sock.h>
#include <net/ip.h>
#include <net/tcp.h>
#include <net/udp.h>
#include <net/icmp.h>
#include <linux/tcp.h>
#include <linux/udp.h>
#include <linux/netfilter_ipv4.h>
#include <net/checksum.h>
#include <linux/route.h>
#include <net/route.h>
#include <net/xfrm.h>

static inline int ip_forward_finish(struct sk_buff *skb) //
{
	struct ip_options * opt	= &(IPCB(skb)->opt);

	IP_INC_STATS_BH(IPSTATS_MIB_OUTFORWDATAGRAMS);

	if (unlikely(opt->optlen)) ////处理转发ip数据包的ip选项 包括记录路由选项和时间戳选项
		ip_forward_options(skb);

	return dst_output(skb); //通过路由缓存将数据包输出 最终调单播的输出函数ip_output或组播的输出函数ip_mc_output
}

int ip_forward(struct sk_buff *skb) //ip数据包的转发
{
	struct iphdr *iph;	/* Our header */
	struct rtable *rt;	/* Route we use */
	struct ip_options * opt	= &(IPCB(skb)->opt);

	if (!xfrm4_policy_check(NULL, XFRM_POLICY_FWD, skb)) //查找IPsec策略数据库
		goto drop;

	if (IPCB(skb)->opt.router_alert && ip_call_ra_chain(skb)) //数据包中有路由警告选项 则调用ip_call_ra_chain将数据包输入给对路由警告感兴趣的用户进程 成功则不再转发数据包
		return NET_RX_SUCCESS;

	if (skb->pkt_type != PACKET_HOST) //目的mac与当前网卡mac相等才转发
		goto drop;

	skb->ip_summed = CHECKSUM_NONE; //在转发过程中会修改ip首部 因此将ip_summed设为CHECKSUM_NONE 在后续输出时还得有软件执行校验和
	
	/*
	 *	According to the RFC, we must first decrease the TTL field. If
	 *	that reaches zero, we must reply an ICMP control message telling
	 *	that the packet's lifetime expired.
	 */
	if (skb->nh.iph->ttl <= 1) //待转发数据包的生存时间为0时 丢弃该报 并发送超时icmp到对端
                goto too_many_hops;

	if (!xfrm4_route_forward(skb)) //进行IPsec路由选路和转发处理 失败则丢弃报文
		goto drop;

	rt = (struct rtable*)skb->dst;

	if (opt->is_strictroute && rt->rt_dst != rt->rt_gateway) ////如果数据包启用严格源路由选项 且数据包的下一跳不是网管 则发送超时icmp到对端
		goto sr_failed;

	/* We are about to mangle packet. Copy it! */
	if (skb_cow(skb, LL_RESERVED_SPACE(rt->u.dst.dev)+rt->u.dst.header_len)) ////确保skb有指定长度的headroom空间 当skb的hr小于指定长度或克隆skb时 会创建skb缓冲区并释放对原包的引用
		goto drop;
	iph = skb->nh.iph;

	/* Decrease ttl after skb cow done */
	ip_decrease_ttl(iph); //经过路由器 IP数据包生存事件递减1

	/*
	 *	We now generate an ICMP HOST REDIRECT giving the route
	 *	we calculated.
	 */
	if (rt->rt_flags&RTCF_DOREDIRECT && !opt->srr) ////如果该数据包的输出路由存在重定向标志 且该数据包中不存在源路由选项 则想发送方发送重定向ICMP报
		ip_rt_send_redirect(skb);

	skb->priority = rt_tos2priority(iph->tos);

	return NF_HOOK(PF_INET, NF_IP_FORWARD, skb, skb->dev, rt->u.dst.dev, ////经netfilter处理后 调ip_forward_finish 完成ip层的转发
		       ip_forward_finish);

sr_failed:
        /*
	 *	Strict routing permits no gatewaying
	 */
         icmp_send(skb, ICMP_DEST_UNREACH, ICMP_SR_FAILED, 0);
         goto drop;

too_many_hops:
        /* Tell the sender its packet died... */ ////发送超时icmp
        IP_INC_STATS_BH(IPSTATS_MIB_INHDRERRORS);
        icmp_send(skb, ICMP_TIME_EXCEEDED, ICMP_EXC_TTL, 0);
drop:
	kfree_skb(skb);
	return NET_RX_DROP;
}

/*
 * Transparent proxy support for Linux/iptables
 *
 * Copyright (c) 2006-2007 BalaBit IT Ltd.
 * Author: Balazs Scheidler, Krisztian Kovacs
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License version 2 as
 * published by the Free Software Foundation.
 *
 */

#include <linux/module.h>
#include <linux/skbuff.h>
#include <linux/ip.h>
#include <net/checksum.h>
#include <net/udp.h>
#include <net/inet_sock.h>

#include <linux/netfilter/x_tables.h>
#include <linux/netfilter_ipv4/ip_tables.h>
#include <linux/netfilter/xt_TPROXY.h>

#include <net/netfilter/ipv4/nf_defrag_ipv4.h>
#include <net/netfilter/nf_tproxy_core.h>

// iptables TPROXY关键字 在内核中做了什么?
//TPROXY关键字作用(需要上层IP_TRANSPARENT配合): 拦截特定的ip/port包 并 打标记
//		打标机的作用是进入正确的表路由

// 说白了就是 原本在tcp层做的事情(tcp_v4_rcv:__inet_lookup) 提前到了ip层的preroute阶段
// https://www.cnblogs.com/lizhaolong/p/16437143.html
// https://zhuanlan.zhihu.com/p/366767578
// https://blog.csdn.net/dog250/article/details/7518054/

struct sock *
nf_tproxy_get_sock_v4(struct net *net, const u8 protocol,
		      const __be32 saddr, const __be32 daddr,
		      const __be16 sport, const __be16 dport,
		      const struct net_device *in, bool listening_only)
{
	struct sock *sk;

	/* look up socket */
	switch (protocol) {
	case IPPROTO_TCP:
		if (listening_only)
			sk = __inet_lookup_listener(net, &tcp_hashinfo,
						    daddr, ntohs(dport),
						    in->ifindex);
		else
			sk = __inet_lookup(net, &tcp_hashinfo,                  // 先查ehash 再查lhash
					   saddr, sport, daddr, dport,
					   in->ifindex);
		break;
	case IPPROTO_UDP:
		sk = udp4_lib_lookup(net, saddr, sport, daddr, dport,
				     in->ifindex);
		break;
	default:
		WARN_ON(1);
		sk = NULL;
	}

	pr_debug("tproxy socket lookup: proto %u %08x:%u -> %08x:%u, listener only: %d, sock %p\n",
		 protocol, ntohl(saddr), ntohs(sport), ntohl(daddr), ntohs(dport), listening_only, sk);

	return sk;
}

static void
nf_tproxy_destructor(struct sk_buff *skb)
{
	struct sock *sk = skb->sk;

	skb->sk = NULL;
	skb->destructor = NULL;

	if (sk)
		nf_tproxy_put_sock(sk);
}

/* consumes sk */
int
nf_tproxy_assign_sock(struct sk_buff *skb, struct sock *sk)     // 转发???
{
	if (inet_sk(sk)->transparent) {
		skb_orphan(skb);
		skb->sk = sk;
		skb->destructor = nf_tproxy_destructor;
		return 1;
	} else
		nf_tproxy_put_sock(sk);

	return 0;
}

static int __init nf_tproxy_init(void)
{
	pr_info("NF_TPROXY: Transparent proxy support initialized, version 4.1.0\n");
	pr_info("NF_TPROXY: Copyright (c) 2006-2007 BalaBit IT Ltd.\n");
	return 0;
}


static unsigned int
tproxy_tg(struct sk_buff *skb, const struct xt_target_param *par)
{
	const struct iphdr *iph = ip_hdr(skb);
	const struct xt_tproxy_target_info *tgi = par->targinfo;
	struct udphdr _hdr, *hp;
	struct sock *sk;

	hp = skb_header_pointer(skb, ip_hdrlen(skb), sizeof(_hdr), &_hdr);              // 实际调用__skb_header_pointer 拿到skb包头
	if (hp == NULL)
		return NF_DROP;

	sk = nf_tproxy_get_sock_v4(dev_net(skb->dev), iph->protocol,                    // 首先检查这个数据包是否存在已经连接套接字中
				   iph->saddr, tgi->laddr ? tgi->laddr : iph->daddr,
				   hp->source, tgi->lport ? tgi->lport : hp->dest,
				   par->in, true);

	/* NOTE: assign_sock consumes our sk reference */
	if (sk && nf_tproxy_assign_sock(skb, sk)) {                                     // 找到了且该sk上设置有IP_TRANSPARENT
		/* This should be in a separate target, but we don't do multiple
		   targets on the same rule yet */
		skb->mark = (skb->mark & ~tgi->mark_mask) ^ tgi->mark_value;

		pr_debug("redirecting: proto %u %08x:%u -> %08x:%u, mark: %x\n",
			 iph->protocol, ntohl(iph->daddr), ntohs(hp->dest),
			 ntohl(tgi->laddr), ntohs(tgi->lport), skb->mark);
		return NF_ACCEPT;
	}

	pr_debug("no socket, dropping: proto %u %08x:%u -> %08x:%u, mark: %x\n",
		 iph->protocol, ntohl(iph->daddr), ntohs(hp->dest),
		 ntohl(tgi->laddr), ntohs(tgi->lport), skb->mark);
	return NF_DROP;
}

static bool tproxy_tg_check(const struct xt_tgchk_param *par)
{
	const struct ipt_ip *i = par->entryinfo;

	if ((i->proto == IPPROTO_TCP || i->proto == IPPROTO_UDP)
	    && !(i->invflags & IPT_INV_PROTO))
		return true;

	pr_info("xt_TPROXY: Can be used only in combination with "
		"either -p tcp or -p udp\n");
	return false;
}

static struct xt_target tproxy_tg_reg __read_mostly = {
	.name		= "TPROXY",
	.family		= AF_INET,
	.table		= "mangle",
	.target		= tproxy_tg,
	.targetsize	= sizeof(struct xt_tproxy_target_info),
	.checkentry	= tproxy_tg_check,
	.hooks		= 1 << NF_INET_PRE_ROUTING,
	.me		= THIS_MODULE,
};

static int __init tproxy_tg_init(void)
{
	nf_defrag_ipv4_enable();
	return xt_register_target(&tproxy_tg_reg);
}

static void __exit tproxy_tg_exit(void)
{
	xt_unregister_target(&tproxy_tg_reg);
}

module_init(tproxy_tg_init);
module_exit(tproxy_tg_exit);
MODULE_LICENSE("GPL");
MODULE_AUTHOR("Krisztian Kovacs");
MODULE_DESCRIPTION("Netfilter transparent proxy (TPROXY) target module.");
MODULE_ALIAS("ipt_TPROXY");

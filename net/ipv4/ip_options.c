/*
 * INET		An implementation of the TCP/IP protocol suite for the LINUX
 *		operating system.  INET is implemented using the  BSD Socket
 *		interface as the means of communication with the user level.
 *
 *		The options processing module for ip.c
 *
 * Version:	$Id: ip_options.c,v 1.21 2001/09/01 00:31:50 davem Exp $
 *
 * Authors:	A.N.Kuznetsov
 *		
 */

#include <linux/capability.h>
#include <linux/module.h>
#include <linux/types.h>
#include <asm/uaccess.h>
#include <linux/skbuff.h>
#include <linux/ip.h>
#include <linux/icmp.h>
#include <linux/netdevice.h>
#include <linux/rtnetlink.h>
#include <net/sock.h>
#include <net/ip.h>
#include <net/icmp.h>
#include <net/route.h>
#include <net/cipso_ipv4.h>

/* 
 * Write options to IP header, record destination address to
 * source route option, address of outgoing interface
 * (we should already know it, so that this  function is allowed be
 * called only after routing decision) and timestamp,
 * if we originate this datagram.
 *
 * daddr is real destination address, next hop is recorded in IP header.
 * saddr is address of outgoing interface.
 */

void ip_options_build(struct sk_buff * skb/*待构建的ip选项的ip数据包*/, struct ip_options * opt/*用于构建ip选项的ip选项信息块结构*/,
			    __be32 daddr/*非下一跳地址而是目的地址*/, struct rtable *rt/*待构建的ip选项的输出路由缓存*/, int is_frag/*待构建ip包是否分片*/)
{
	unsigned char * iph = skb->nh.raw; //获取skb中ip首部存储地址

	memcpy(&(IPCB(skb)->opt), opt, sizeof(struct ip_options)); //将源ip选项信息块&其后的选项数据复制到skb对应存储区中 &将opt指向skb中ip_optinos结构     is_data为0即此结构后不跟选项内容 skb选项信息跟内容分别存放
	memcpy(iph+sizeof(struct iphdr), opt->__data, opt->optlen);
	opt = &(IPCB(skb)->opt);
	opt->is_data = 0;

	if (opt->srr) //有严格路由选项 则将目的地址复制到源路由选项地址列表末尾 iph[opt->ssr+1]即是取得该选项的长度
		memcpy(iph+opt->srr+iph[opt->srr+1]-4, &daddr, 4);

	if (!is_frag) { //如果该数据包不是ip分片 & 存在记录路由|时间戳选项 则通过输出路由缓存获取源地址填写到记录路由选项|时间戳选项的地址部分中 获取当前的时间填写到时间戳选项中
		if (opt->rr_needaddr)
			ip_rt_get_source(iph+opt->rr+iph[opt->rr+2]-5, rt);
		if (opt->ts_needaddr)
			ip_rt_get_source(iph+opt->ts+iph[opt->ts+2]-9, rt);
		if (opt->ts_needtime) {
			struct timeval tv;
			__be32 midtime;
			do_gettimeofday(&tv);
			midtime = htonl((tv.tv_sec % 86400) * 1000 + tv.tv_usec / 1000);
			memcpy(iph+opt->ts+iph[opt->ts+2]-5, &midtime, 4);
		}
		return;
	}
	if (opt->rr) { //如果分片 & 存在记录路由|时间戳选项 则将这些选项替换成无操作
		memset(iph+opt->rr, IPOPT_NOP, iph[opt->rr+1]);
		opt->rr = 0;
		opt->rr_needaddr = 0;
	}
	if (opt->ts) {
		memset(iph+opt->ts, IPOPT_NOP, iph[opt->ts+1]);
		opt->ts = 0;
		opt->ts_needaddr = opt->ts_needtime = 0;
	}
}

/* 
 * Provided (sopt, skb) points to received options,
 * build in dopt compiled option set appropriate for answering.
 * i.e. invert SRR option, copy anothers,
 * and grab room in RR/TS options.
 *
 * NOTE: dopt cannot point to skb.
 */

int ip_options_echo(struct ip_options * dopt, struct sk_buff * skb) //从收到的ip数据包skb中复制选项内容到指定ip_options结构中 常用于创建icmp响应报文 | 收到错误报文后发给对端icmp差错报文 | tcp中发给对方ack
{
	struct ip_options *sopt;
	unsigned char *sptr, *dptr;
	int soffset, doffset;
	int	optlen;
	__be32	daddr;

	memset(dopt, 0, sizeof(struct ip_options));

	dopt->is_data = 1;

	sopt = &(IPCB(skb)->opt);

	if (sopt->optlen == 0) { //没有ip选项
		dopt->optlen = 0;
		return 0;
	}

	sptr = skb->nh.raw; //获取ip包首部起始地址
	dptr = dopt->__data;

	if (skb->dst) //获取该数据包的目的地址 用于记录路由选项 当存在路由选项时 为路由项的rt_spec_dst字段 该字段称为首选源地址 否则是数据包ip首部中的目的地址 其实就是当前网卡的地址
		daddr = ((struct rtable*)skb->dst)->rt_spec_dst;
	else
		daddr = skb->nh.iph->daddr;

	if (sopt->rr) { //复制记录路由选项
		optlen  = sptr[sopt->rr+1];
		soffset = sptr[sopt->rr+2];
		dopt->rr = dopt->optlen + sizeof(struct iphdr); //将记录路由选项内容复制到目标选项信息块dopt的__data字段开始区域处
		memcpy(dptr, sptr+sopt->rr, optlen);
		if (sopt->rr_needaddr && soffset <= optlen) { //如果源数据包中需要记录路由 而剩余空间不足放下一个地址值 则出错返回
			if (soffset + 3 > optlen)
				return -EINVAL;
			dptr[2] = soffset + 4;
			dopt->rr_needaddr = 1;
		}
		dptr += optlen; //更新选项指针
		dopt->optlen += optlen;
	}
	if (sopt->ts) { //复制时间戳选项
		optlen = sptr[sopt->ts+1];
		soffset = sptr[sopt->ts+2];
		dopt->ts = dopt->optlen + sizeof(struct iphdr);
		memcpy(dptr, sptr+sopt->ts, optlen);
		if (soffset <= optlen) {
			if (sopt->ts_needaddr) {
				if (soffset + 3 > optlen)
					return -EINVAL;
				dopt->ts_needaddr = 1;
				soffset += 4;
			}
			if (sopt->ts_needtime) { //在需要记录时间戳情况下 当选项标志位0|1时 | 当选项标志位3&指针指向的地址类型不是RTN_LOCAL时 即本地不是数据包接收方 置ts_needtime为1
				if (soffset + 3 > optlen)
					return -EINVAL;
				if ((dptr[3]&0xF) != IPOPT_TS_PRESPEC) {
					dopt->ts_needtime = 1;
					soffset += 4;
				} else {
					dopt->ts_needtime = 0;

					if (soffset + 8 <= optlen) {
						__be32 addr;

						memcpy(&addr, sptr+soffset-1, 4);
						if (inet_addr_type(addr) != RTN_LOCAL) {
							dopt->ts_needtime = 1;
							soffset += 8;
						}
					}
				}
			}
			dptr[2] = soffset;
		}
		dptr += optlen;
		dopt->optlen += optlen;
	}
	if (sopt->srr) { //复制源路由选项
		unsigned char * start = sptr+sopt->srr;
		__be32 faddr;

		optlen  = start[1];
		soffset = start[2];
		doffset = 0;
		if (soffset > optlen)
			soffset = optlen + 1;
		soffset -= 4;
		if (soffset > 3) {
			memcpy(&faddr, &start[soffset-1], 4);
			for (soffset-=4, doffset=4; soffset > 3; soffset-=4, doffset+=4)
				memcpy(&dptr[doffset-1], &start[soffset-1], 4);
			/*
			 * RFC1812 requires to fix illegal source routes.
			 */
			if (memcmp(&skb->nh.iph->saddr, &start[soffset+3], 4) == 0)
				doffset -= 4;
		}
		if (doffset > 3) {
			memcpy(&start[doffset-1], &daddr, 4);
			dopt->faddr = faddr;
			dptr[0] = start[0];
			dptr[1] = doffset+3;
			dptr[2] = 4;
			dptr += doffset+3;
			dopt->srr = dopt->optlen + sizeof(struct iphdr);
			dopt->optlen += doffset+3;
			dopt->is_strictroute = sopt->is_strictroute;
		}
	}
	if (sopt->cipso) { //复制商业ip安全选项
		optlen  = sptr[sopt->cipso+1];
		dopt->cipso = dopt->optlen+sizeof(struct iphdr);
		memcpy(dptr, sptr+sopt->cipso, optlen);
		dptr += optlen;
		dopt->optlen += optlen;
	}
	while (dopt->optlen & 3) { //对齐
		*dptr++ = IPOPT_END;
		dopt->optlen++;
	}
	return 0;
}

/*
 *	Options "fragmenting", just fill options not
 *	allowed in fragments with NOOPs.
 *	Simple and stupid 8), but the most efficient way.
 */

void ip_options_fragment(struct sk_buff * skb)  //清理掉复制标志为0的选项 将他们填充为无操作
{
	unsigned char * optptr = skb->nh.raw + sizeof(struct iphdr);
	struct ip_options * opt = &(IPCB(skb)->opt);
	int  l = opt->optlen;
	int  optlen;

	while (l > 0) { //遍历所有选项 对无需复制到分片的选项 将其值改为无操作
		switch (*optptr) {
		case IPOPT_END:
			return;
		case IPOPT_NOOP:
			l--;
			optptr++;
			continue;
		}
		optlen = optptr[1];
		if (optlen<2 || optlen>l)
		  return;
		if (!IPOPT_COPIED(*optptr))
			memset(optptr, IPOPT_NOOP, optlen);
		l -= optlen;
		optptr += optlen;
	}
	opt->ts = 0;
	opt->rr = 0;
	opt->rr_needaddr = 0;
	opt->ts_needaddr = 0;
	opt->ts_needtime = 0;
	return;
}

/*
 * Verify options and fill pointers in struct options.
 * Caller should clear *opt, and set opt->data.
 * If opt == NULL, then skb->data should point to IP header.
 */
												//opt sbk不能同时为NULL  & 当opt的is_data为0时 skb也不能为NULL
int ip_options_compile(struct ip_options * opt, struct sk_buff * skb) //ip_optinos_get_finish & ip_rcv_optinons调用此函数 分别为发收方向 发送时调ip_option_compile(opt, NULL) 接收调ip_option_compile(NULL, skb)
{                                                  //发送时 opt为传入传出参数 选项存在opt的_data字段起始区域   接收时数据在skb的nh.raw指向的ip首部中 解析到的信息保存到skb的cb中
	int l;
	unsigned char * iph;
	unsigned char * optptr;
	int optlen;
	unsigned char * pp_ptr = NULL;
	struct rtable *rt = skb ? (struct rtable*)skb->dst : NULL;

	if (!opt) {
		opt = &(IPCB(skb)->opt);
		iph = skb->nh.raw;
		opt->optlen = ((struct iphdr *)iph)->ihl*4 - sizeof(struct iphdr);
		optptr = iph + sizeof(struct iphdr);
		opt->is_data = 0;
	} else {
		optptr = opt->is_data ? opt->__data : (unsigned char*)&(skb->nh.iph[1]);
		iph = optptr - sizeof(struct iphdr);
	}

	for (l = opt->optlen; l > 0; ) {
		switch (*optptr) {
		      case IPOPT_END:
			for (optptr++, l--; l>0; optptr++, l--) {
				if (*optptr != IPOPT_END) {
					*optptr = IPOPT_END;
					opt->is_changed = 1;
				}
			}
			goto eol;
		      case IPOPT_NOOP:
			l--;
			optptr++;
			continue;
		}
		optlen = optptr[1];
		if (optlen<2 || optlen>l) {
			pp_ptr = optptr;
			goto error;
		}
		switch (*optptr) { //处理源路由选项
		      case IPOPT_SSRR:
		      case IPOPT_LSRR:
			if (optlen < 3) { //源路由选项长度是否有效 指针是否有效
				pp_ptr = optptr + 1;
				goto error;
			}
			if (optptr[2] < 4) {
				pp_ptr = optptr + 2;
				goto error;
			}
			/* NB: cf RFC-1812 5.2.4.1 */
			if (opt->srr) {
				pp_ptr = optptr;
				goto error;
			}
			if (!skb) { //针对发送 再次校验选项中的指针&长度有效性 对于选项指针值最小值为4 对于选项长度值 除了选项类型 长度 以及选项指针三字节外 至少应该可以容纳一个ip地址 且扣除了前面三字节应4字节对齐 作为发送方
				if (optptr[2] != 4 || optlen < 7 || ((optlen-3) & 3)) {
					pp_ptr = optptr + 1;
					goto error;
				}
				memcpy(&opt->faddr, &optptr[3], 4);
				if (optlen > 7)
					memmove(&optptr[3], &optptr[7], optlen-7); //应取出第一个地址作为下一跳地址 & 在路径列表中多于一个地址时 将剩余所有地址往前移动一个位置
			}
			opt->is_strictroute = (optptr[0] == IPOPT_SSRR);
			opt->srr = optptr - iph; //记录路由选项在ip首部中的偏移量
			break;
		      case IPOPT_RR: //处理记录路由选项
			if (opt->rr) {
				pp_ptr = optptr;
				goto error;
			}
			if (optlen < 3) { //校验待处理记录路由选项的长度 指针
				pp_ptr = optptr + 1;
				goto error;
			}
			if (optptr[2] < 4) {
				pp_ptr = optptr + 2;
				goto error;
			}
			if (optptr[2] <= optlen) { //接收: 将本地源地址填入记录路由选项中 & 设置需重新计算校验和标志 最后调整选项指针
				if (optptr[2]+3 > optlen) {
					pp_ptr = optptr + 2;
					goto error;
				}
				if (skb) {
					memcpy(&optptr[optptr[2]-1], &rt->rt_spec_dst, 4);
					opt->is_changed = 1;
				}
				optptr[2] += 4;
				opt->rr_needaddr = 1;
			}
			opt->rr = optptr - iph; //标识记录路由选项在ip首部中的偏移量
			break;
		      case IPOPT_TIMESTAMP: //时间戳选项处理
			if (opt->ts) {
				pp_ptr = optptr;
				goto error;
			}
			if (optlen < 4) {
				pp_ptr = optptr + 1;
				goto error;
			}
			if (optptr[2] < 5) {
				pp_ptr = optptr + 2;
				goto error;
			}
			if (optptr[2] <= optlen) { //时间戳区域未被填满时 检测时间戳选项指针是否有效
				__be32 *timeptr = NULL;
				if (optptr[2]+3 > optptr[1]) {
					pp_ptr = optptr + 2;
					goto error;
				}
				switch (optptr[3]&0xF) {
				      case IPOPT_TS_TSONLY: //如果只记录时间戳 则标记时间戳选项在ip首部中的偏移量 同时若转发数据包 则取得时间戳的记录位置 后续将会把时间戳复制到该位置
					opt->ts = optptr - iph;
					if (skb) 
						timeptr = (__be32*)&optptr[optptr[2]-1];
					opt->ts_needtime = 1;
					optptr[2] += 4;
					break;
				      case IPOPT_TS_TSANDADDR: //记录时间戳 & ip   首先检测剩余空间是否够记录一个ip&时间 够则还需确保选项中指定地址不是广播地址 然后取得时间戳的记录位置
					if (optptr[2]+7 > optptr[1]) {
						pp_ptr = optptr + 2;
						goto error;
					}
					opt->ts = optptr - iph;
					if (skb) {
						memcpy(&optptr[optptr[2]-1], &rt->rt_spec_dst, 4);
						timeptr = (__be32*)&optptr[optptr[2]+3];
					}
					opt->ts_needaddr = 1;
					opt->ts_needtime = 1;
					optptr[2] += 8;
					break;
				      case IPOPT_TS_PRESPEC:
					if (optptr[2]+7 > optptr[1]) {
						pp_ptr = optptr + 2;
						goto error;
					}
					opt->ts = optptr - iph;
					{
						__be32 addr;
						memcpy(&addr, &optptr[optptr[2]-1], 4);
						if (inet_addr_type(addr) == RTN_UNICAST)
							break;
						if (skb)
							timeptr = (__be32*)&optptr[optptr[2]+3];
					}
					opt->ts_needtime = 1;
					optptr[2] += 8;
					break;
				      default:
					if (!skb && !capable(CAP_NET_RAW)) {
						pp_ptr = optptr + 3;
						goto error;
					}
					break;
				}
				if (timeptr) { //如果之前取得了时间戳的记录位置 则取得时间值&复制该值得记录位置 记得设置选项信息块opt的is_changed字段
					struct timeval tv;
					__be32  midtime;
					do_gettimeofday(&tv);
					midtime = htonl((tv.tv_sec % 86400) * 1000 + tv.tv_usec / 1000);
					memcpy(timeptr, &midtime, sizeof(__be32));
					opt->is_changed = 1;
				}
			} else {
				unsigned overflow = optptr[3]>>4; //时间戳区已满 此时如果OF标志溢出 则跳转到出错处理 否则若是接收则重新计算OF标志
				if (overflow == 15) {
					pp_ptr = optptr + 3;
					goto error;
				}
				opt->ts = optptr - iph;
				if (skb) {
					optptr[3] = (optptr[3]&0xF)|((overflow+1)<<4);
					opt->is_changed = 1;
				}
			}
			break;
		      case IPOPT_RA: //处理路由警告选项
			if (optlen < 4) {
				pp_ptr = optptr + 1;
				goto error;
			}
			if (optptr[2] == 0 && optptr[3] == 0) //警告选项值有效 则标记路由器警告选项在ip首部的偏移量
				opt->router_alert = optptr - iph;
			break;
		      case IPOPT_CIPSO: //处理商业ip选项
			if ((!skb && !capable(CAP_NET_RAW)) || opt->cipso) {
				pp_ptr = optptr;
				goto error;
			}
			opt->cipso = optptr - iph;
		        if (cipso_v4_validate(&optptr)) {
				pp_ptr = optptr;
				goto error;
			}
			break;
		      case IPOPT_SEC: //对于流标识选项&安全选项 无需做特别处理 但如果是接收数据包 则操作选项的进程必须有操作raw套接口&packet套接口的能力
		      case IPOPT_SID:
		      default:
			if (!skb && !capable(CAP_NET_RAW)) {
				pp_ptr = optptr;
				goto error;
			}
			break;
		}
		l -= optlen; //每处理完一个选项 将指针后移到下一个选项 以便继续处理后续选项
		optptr += optlen;
	}

eol: //遇到了选项列表结束符
	if (!pp_ptr)
		return 0;

error:
	if (skb) {
		icmp_send(skb, ICMP_PARAMETERPROB, 0, htonl((pp_ptr-iph)<<24)); //如果是接收数据包错误 则需给该ip数据包的发送方发一个参数问题的icmp报文
	}
	return -EINVAL;
}


/*
 *	Undo all the changes done by ip_options_compile().
 */

void ip_options_undo(struct ip_options * opt) //ip_optinos_compile处理过的ip选项信息块 如果数据包中存在源路由选项 记录路由选项 时间戳选项 将他们恢复到调用ip_options_compile之前
{
	if (opt->srr) { //如果存在源路由选项 则路径列表中的所有地址往后移动一个位置 然后将目的地址即下一跳 重新复制到路径列表的第一个地址处
		unsigned  char * optptr = opt->__data+opt->srr-sizeof(struct  iphdr);
		memmove(optptr+7, optptr+3, optptr[1]-7);
		memcpy(optptr+3, &opt->faddr, 4);
	}
	if (opt->rr_needaddr) { //存在记录路由选项 则将保存到路径列表中的本地地址删除
		unsigned  char * optptr = opt->__data+opt->rr-sizeof(struct  iphdr);
		optptr[2] -= 4;
		memset(&optptr[optptr[2]-1], 0, 4);
	}
	if (opt->ts) { //存在时间  则根据记录时间戳和记录地址标志 将保存的时间戳|本地地址删除
		unsigned  char * optptr = opt->__data+opt->ts-sizeof(struct  iphdr);
		if (opt->ts_needtime) {
			optptr[2] -= 4;
			memset(&optptr[optptr[2]-1], 0, 4);
			if ((optptr[3]&0xF) == IPOPT_TS_PRESPEC)
				optptr[2] -= 4;
		}
		if (opt->ts_needaddr) {
			optptr[2] -= 4;
			memset(&optptr[optptr[2]-1], 0, 4);
		}
	}
}

static struct ip_options *ip_options_get_alloc(const int optlen)
{
	struct ip_options *opt = kmalloc(sizeof(*opt) + ((optlen + 3) & ~3),
					 GFP_KERNEL);
	if (opt)
		memset(opt, 0, sizeof(*opt));
	return opt;
}

static int ip_options_get_finish(struct ip_options **optp,
				 struct ip_options *opt, int optlen)
{
	while (optlen & 3) //如果ip选项内容不是以4字节对齐 则将未对齐部分用选项表结束符填充
		opt->__data[optlen++] = IPOPT_END;
	opt->optlen = optlen; //设置ip选项信息块中选项长度&有数据标志
	opt->is_data = 1;
	if (optlen && ip_options_compile(opt, NULL)) { //解析ip选项信息块各字段值
		kfree(opt);
		return -EINVAL;
	}
	kfree(*optp); //返回新创建&已填充解析后信息的ip选项信息块
	*optp = opt;
	return 0;
}

int ip_options_get_from_user(struct ip_options **optp, unsigned char __user *data, int optlen)
{
	struct ip_options *opt = ip_options_get_alloc(optlen);

	if (!opt)
		return -ENOMEM;
	if (optlen && copy_from_user(opt->__data, data, optlen)) {
		kfree(opt);
		return -EFAULT;
	}
	return ip_options_get_finish(optp, opt, optlen);
}

int ip_options_get(struct ip_options **optp, unsigned char *data, int optlen)
{
	struct ip_options *opt = ip_options_get_alloc(optlen); //为控制信息分配ip选项信息块空间

	if (!opt)
		return -ENOMEM;
	if (optlen)
		memcpy(opt->__data, data, optlen);
	return ip_options_get_finish(optp, opt, optlen);
}

void ip_forward_options(struct sk_buff *skb) //会向将转发的数据包添加所需的关于本地ip的信息 包括记录路由选项和时间戳选项
{
	struct   ip_options * opt	= &(IPCB(skb)->opt);
	unsigned char * optptr;
	struct rtable *rt = (struct rtable*)skb->dst;
	unsigned char *raw = skb->nh.raw;

	if (opt->rr_needaddr) { //如果需要记录ip地址 则获取本地地址&设置到ip记录路由选项中
		optptr = (unsigned char *)raw + opt->rr;
		ip_rt_get_source(&optptr[optptr[2]-5], rt);
		opt->is_changed = 1;
	}
	if (opt->srr_is_hit) { //如果目的地址是 从源路由选项指定的 则还需要判断输出路由缓存的目的地址是否存在于源路由选项中 如果存在 则根据输出路由缓存的目的地址重新设置ip首部中的目的地址
		int srrptr, srrspace;

		optptr = raw + opt->srr;

		for ( srrptr=optptr[2], srrspace = optptr[1];
		     srrptr <= srrspace;
		     srrptr += 4
		     ) {
			if (srrptr + 3 > srrspace)
				break;
			if (memcmp(&rt->rt_dst, &optptr[srrptr-1], 4) == 0)
				break;
		}
		if (srrptr + 3 <= srrspace) {
			opt->is_changed = 1;
			ip_rt_get_source(&optptr[srrptr-1], rt);
			skb->nh.iph->daddr = rt->rt_dst;
			optptr[2] = srrptr+4;
		} else if (net_ratelimit())
			printk(KERN_CRIT "ip_forward(): Argh! Destination lost!\n");
		if (opt->ts_needaddr) {
			optptr = raw + opt->ts;
			ip_rt_get_source(&optptr[optptr[2]-9], rt);
			opt->is_changed = 1;
		}
	}
	if (opt->is_changed) { //一旦ip首部做了修改 就得重新计算ip数据包首部的校验和
		opt->is_changed = 0;
		ip_send_check(skb->nh.iph);
	}
}

int ip_options_rcv_srr(struct sk_buff *skb)         // 检查输入数据包中的宽松路由&严格路由选项 并根据源路由选项更新ip数据包下一跳地址
{
	struct ip_options *opt = &(IPCB(skb)->opt);
	int srrspace, srrptr;
	__be32 nexthop;
	struct iphdr *iph = skb->nh.iph;
	unsigned char * optptr = skb->nh.raw + opt->srr;
	struct rtable *rt = (struct rtable*)skb->dst;
	struct rtable *rt2;
	int err;

	if (!opt->srr)                                  // 如果待处理的数据包中没有宽松|严格路由选项 则返回
		return 0;

	if (skb->pkt_type != PACKET_HOST)               // 待处理ip数据包其接收方必须是本地主机 否则返回参数无效错误
		return -EINVAL;
	if (rt->rt_type == RTN_UNICAST) {               // 在路由类型为RTN_UNICAST 即网关|直接连接路由情况下执行严格路由会有问题的 此时会发送参数错误icmp差错报文给发送方
		if (!opt->is_strictroute)
			return 0;
		icmp_send(skb, ICMP_PARAMETERPROB, 0, htonl(16<<24));
		return -EINVAL;
	}
	if (rt->rt_type != RTN_LOCAL)                   // 待处理ip数据包的路由目的地址必须为本机主机 否则返回参数无效错误
		return -EINVAL;

	for (srrptr=optptr[2], srrspace = optptr[1]; srrptr <= srrspace; srrptr += 4) { // 根据源路由选项更新ip数据包的下一跳地址 // 遍历源路由选项中的地址
		if (srrptr + 3 > srrspace) {                                                // 校验源路由选项的路径列表是否还能至少容纳下一个ip地址 如果不能则发参数问题icmp差错报文
			icmp_send(skb, ICMP_PARAMETERPROB, 0, htonl((opt->srr+2)<<24));
			return -EINVAL;
		}
		memcpy(&nexthop, &optptr[srrptr-1], 4);     // 通过输入路由方式来判断是否抵达源路由选项中的某一站 一旦确定本地为源路由选项中的某一站 则获取下一跳的ip地址作为该数据包的目的地址 &设is_changed 表示ip数据包做了修改

		rt = (struct rtable*)skb->dst;
		skb->dst = NULL;
		err = ip_route_input(skb, nexthop, iph->saddr, iph->tos, skb->dev);
		rt2 = (struct rtable*)skb->dst;
		if (err || (rt2->rt_type != RTN_UNICAST && rt2->rt_type != RTN_LOCAL)) {
			ip_rt_put(rt2);
			skb->dst = &rt->u.dst;
			return -EINVAL;
		}
		ip_rt_put(rt);
		if (rt2->rt_type != RTN_LOCAL)
			break;
		/* Superfast 8) loopback forward */
		memcpy(&iph->daddr, &optptr[srrptr-1], 4); // 一旦本地为源路由选项中的某一站 则获取下一跳的ip地址作为该数据包的目的地址 &设is_changed 表示ip数据包做了修改
		opt->is_changed = 1;
	}
	if (srrptr <= srrspace) {                       // 如果源路由选项的路径列表没有遍历完 则说明该ip数据包的目的地址是从源路由选项选出的 因此需要设置srr_is_hit标志 待转发时需要进一步处理 同时还需设置is_changed 标识需重新计算ip数据包的首部校验和
		opt->srr_is_hit = 1;
		opt->is_changed = 1;
	}
	return 0;
}

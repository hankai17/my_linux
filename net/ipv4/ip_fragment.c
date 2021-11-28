/*
 * INET		An implementation of the TCP/IP protocol suite for the LINUX
 *		operating system.  INET is implemented using the  BSD Socket
 *		interface as the means of communication with the user level.
 *
 *		The IP fragmentation functionality.
 *		
 * Version:	$Id: ip_fragment.c,v 1.59 2002/01/12 07:54:56 davem Exp $
 *
 * Authors:	Fred N. van Kempen <waltje@uWalt.NL.Mugnet.ORG>
 *		Alan Cox <Alan.Cox@linux.org>
 *
 * Fixes:
 *		Alan Cox	:	Split from ip.c , see ip_input.c for history.
 *		David S. Miller :	Begin massive cleanup...
 *		Andi Kleen	:	Add sysctls.
 *		xxxx		:	Overlapfrag bug.
 *		Ultima          :       ip_expire() kernel panic.
 *		Bill Hawes	:	Frag accounting and evictor fixes.
 *		John McDonald	:	0 length frag bug.
 *		Alexey Kuznetsov:	SMP races, threading, cleanup.
 *		Patrick McHardy :	LRU queue of frag heads for evictor.
 */

#include <linux/compiler.h>
#include <linux/module.h>
#include <linux/types.h>
#include <linux/mm.h>
#include <linux/jiffies.h>
#include <linux/skbuff.h>
#include <linux/list.h>
#include <linux/ip.h>
#include <linux/icmp.h>
#include <linux/netdevice.h>
#include <linux/jhash.h>
#include <linux/random.h>
#include <net/sock.h>
#include <net/ip.h>
#include <net/icmp.h>
#include <net/checksum.h>
#include <net/inetpeer.h>
#include <linux/tcp.h>
#include <linux/udp.h>
#include <linux/inet.h>
#include <linux/netfilter_ipv4.h>

/* NOTE. Logic of IP defragmentation is parallel to corresponding IPv6
 * code now. If you change something here, _PLEASE_ update ipv6/reassembly.c
 * as well. Or notify me, at least. --ANK
 */

/* Fragment cache limits. We will commit 256K at one time. Should we
 * cross that limit we will prune down to 192K. This should cope with
 * even the most extreme cases without allowing an attacker to measurably
 * harm machine performance.
 */
int sysctl_ipfrag_high_thresh __read_mostly = 256*1024;
int sysctl_ipfrag_low_thresh __read_mostly = 192*1024;

int sysctl_ipfrag_max_dist __read_mostly = 64;

/* Important NOTE! Fragment queue must be destroyed before MSL expires.
 * RFC791 is wrong proposing to prolongate timer each fragment arrival by TTL.
 */
int sysctl_ipfrag_time __read_mostly = IP_FRAG_TIME;

struct ipfrag_skb_cb
{
	struct inet_skb_parm	h;
	int			offset;
};

#define FRAG_CB(skb)	((struct ipfrag_skb_cb*)((skb)->cb))

/* Describe an entry in the "incomplete datagrams" queue. */
struct ipq {
	struct hlist_node list;
	struct list_head lru_list;	/* lru list member 			*/
	u32		user;
	__be32		saddr;
	__be32		daddr;
	__be16		id;
	u8		protocol;
	u8		last_in;
#define COMPLETE		4
#define FIRST_IN		2
#define LAST_IN			1

	struct sk_buff	*fragments;	/* linked list of received fragments	*/
	int		len;		/* total length of original datagram	*/
	int		meat;
	spinlock_t	lock;
	atomic_t	refcnt;
	struct timer_list timer;	/* when will this queue expire?		*/
	struct timeval	stamp;
	int             iif;
	unsigned int    rid;
	struct inet_peer *peer;
};

/* Hash table. */

#define IPQ_HASHSZ	64

/* Per-bucket lock is easy to add now. */
static struct hlist_head ipq_hash[IPQ_HASHSZ];
static DEFINE_RWLOCK(ipfrag_lock);
static u32 ipfrag_hash_rnd;
static LIST_HEAD(ipq_lru_list);
int ip_frag_nqueues = 0;

static __inline__ void __ipq_unlink(struct ipq *qp)
{
	hlist_del(&qp->list);
	list_del(&qp->lru_list);
	ip_frag_nqueues--;
}

static __inline__ void ipq_unlink(struct ipq *ipq)
{
	write_lock(&ipfrag_lock);
	__ipq_unlink(ipq);
	write_unlock(&ipfrag_lock);
}

static unsigned int ipqhashfn(__be16 id, __be32 saddr, __be32 daddr, u8 prot)
{
	return jhash_3words((__force u32)id << 16 | prot,
			    (__force u32)saddr, (__force u32)daddr,
			    ipfrag_hash_rnd) & (IPQ_HASHSZ - 1);
}

static struct timer_list ipfrag_secret_timer;
int sysctl_ipfrag_secret_interval __read_mostly = 10 * 60 * HZ;

static void ipfrag_secret_rebuild(unsigned long dummy) //ipfrag_secret_timer定时器的例程 用来对全局的ipq散列表进行重组
{
	unsigned long now = jiffies;
	int i;

	write_lock(&ipfrag_lock); //ipfrag_lock是ipq散列表的读写锁 在对散列表重构前需要对此锁进行写上锁
	get_random_bytes(&ipfrag_hash_rnd, sizeof(u32)); //调get_random_bytes 重新获取ipfrag_hash_rnd随机值
	for (i = 0; i < IPQ_HASHSZ; i++) { //遍历ipq散列表中所有ipq 根据新的ipfrag_hash_rnd值把这些ipq重新连接到散列表相应的桶中
		struct ipq *q;
		struct hlist_node *p, *n;

		hlist_for_each_entry_safe(q, p, n, &ipq_hash[i], list) {
			unsigned int hval = ipqhashfn(q->id, q->saddr,
						      q->daddr, q->protocol);

			if (hval != i) {
				hlist_del(&q->list);

				/* Relink to new hash chain. */
				hlist_add_head(&q->list, &ipq_hash[hval]);
			}
		}
	}
	write_unlock(&ipfrag_lock); //写解锁ipfrag_lock

	mod_timer(&ipfrag_secret_timer, now + sysctl_ipfrag_secret_interval); //重新设置重构定时器的下次到期时间
}

atomic_t ip_frag_mem = ATOMIC_INIT(0);	/* Memory used for fragments */

/* Memory Tracking Functions. */
static __inline__ void frag_kfree_skb(struct sk_buff *skb, int *work)
{
	if (work)
		*work -= skb->truesize;
	atomic_sub(skb->truesize, &ip_frag_mem);
	kfree_skb(skb);
}

static __inline__ void frag_free_queue(struct ipq *qp, int *work)
{
	if (work)
		*work -= sizeof(struct ipq);
	atomic_sub(sizeof(struct ipq), &ip_frag_mem);
	kfree(qp);
}

static __inline__ struct ipq *frag_alloc_queue(void)
{
	struct ipq *qp = kmalloc(sizeof(struct ipq), GFP_ATOMIC);

	if(!qp)
		return NULL;
	atomic_add(sizeof(struct ipq), &ip_frag_mem);
	return qp;
}


/* Destruction primitives. */

/* Complete destruction of ipq. */
static void ip_frag_destroy(struct ipq *qp, int *work)
{
	struct sk_buff *fp;

	BUG_TRAP(qp->last_in&COMPLETE);
	BUG_TRAP(del_timer(&qp->timer) == 0);

	if (qp->peer)
		inet_putpeer(qp->peer);

	/* Release all fragment data. */
	fp = qp->fragments;
	while (fp) {
		struct sk_buff *xp = fp->next;

		frag_kfree_skb(fp, work);
		fp = xp;
	}

	/* Finally, release the queue descriptor itself. */
	frag_free_queue(qp, work);
}

static __inline__ void ipq_put(struct ipq *ipq, int *work) //释放ipq及分片 封装了ip_frag_destroy 实现了对ipq和分片的释放 调用ip_frag_destroy之前 会先用atomic_dec_and_test对引用计数判断
{
	if (atomic_dec_and_test(&ipq->refcnt))
		ip_frag_destroy(ipq, work);
}

/* Kill ipq entry. It is not destroyed immediately,
 * because caller (and someone more) holds reference count.
 */
static void ipq_kill(struct ipq *ipq) //将组装定时器超时的ipq上从ipq散列表&ipq_lru_list链表中删除 但并不释放 首先停止该ipq上的组装定时器 递减ipq引用计数
{
	if (del_timer(&ipq->timer))
		atomic_dec(&ipq->refcnt);

	if (!(ipq->last_in & COMPLETE)) {
		ipq_unlink(ipq); //调ipq_unlink 从散列表和链表中都摘除 引用计数再减一 最后设置ipq的last_in为COMPLETE态 只有COMPLETE态的ipq才能被释放
		atomic_dec(&ipq->refcnt);
		ipq->last_in |= COMPLETE;
	}
}

/* Memory limiting on fragments.  Evictor trashes the oldest 
 * fragment queue until we are back under the threshold.
 */
static void ip_evictor(void) //ipfrag_high_thresh用于控制ip组装所占内存大小  总的实时大小为全局变量ip_frag_mem 当大于ipfrag_high_thresh时 调ip_evictor对散列表清理
{
	struct ipq *qp;
	struct list_head *tmp;
	int work;

	work = atomic_read(&ip_frag_mem) - sysctl_ipfrag_low_thresh;
	if (work <= 0)
		return;

	while (work > 0) {
		read_lock(&ipfrag_lock);
		if (list_empty(&ipq_lru_list)) {
			read_unlock(&ipfrag_lock);
			return;
		}
		tmp = ipq_lru_list.next;
		qp = list_entry(tmp, struct ipq, lru_list);
		atomic_inc(&qp->refcnt); //遍历qp增加引用计数
		read_unlock(&ipfrag_lock);

		spin_lock(&qp->lock);
		if (!(qp->last_in&COMPLETE))
			ipq_kill(qp); //如果分片未到齐 则从散列表&列表中摘除 并不释放
		spin_unlock(&qp->lock);

		ipq_put(qp, &work); //真正删除ipq&所有分片
		IP_INC_STATS_BH(IPSTATS_MIB_REASMFAILS);
	}
}

/*
 * Oops, a fragment queue timed out.  Kill it and send an ICMP reply. //一个ip包分片有可能不会都到达目的地 这样会占大量资源 此外也是为了抵御dos 因此需要设置一个时钟 一旦超时 数据包分片还未到达 则将已到分片都清除
 */
static void ip_expire(unsigned long arg) //组装超时定时器: 当定时器被激活 清除在规定时机内还没完成组装的ipq及所有分片
{
	struct ipq *qp = (struct ipq *) arg;

	spin_lock(&qp->lock); //操作分片链表前先上锁ipq自旋锁

	if (qp->last_in & COMPLETE) //若ipq已经是COMPLETE态 则不处理 直接跳转到释放ipq&其所有分片处
		goto out;

	ipq_kill(qp); //将ipq从散列表中&ipq_lru_list中摘除

	IP_INC_STATS_BH(IPSTATS_MIB_REASMTIMEOUT); //对MIB的ReasmTimeout和ReasmFails数据进行统计
	IP_INC_STATS_BH(IPSTATS_MIB_REASMFAILS);

	if ((qp->last_in&FIRST_IN) && qp->fragments != NULL) {
		struct sk_buff *head = qp->fragments;
		/* Send an ICMP "Fragment Reassembly Timeout" message. */
		if ((head->dev = dev_get_by_index(qp->iif)) != NULL) {
			icmp_send(head, ICMP_TIME_EXCEEDED, ICMP_EXC_FRAGTIME, 0); //如果第一个分片已经到达 则发送分片组装超时ICMP出错报文
			dev_put(head->dev);
		}
	}
out:
	spin_unlock(&qp->lock); //在完成ipq分片链表操作后解自旋锁
	ipq_put(qp, NULL); //释放ipq&所有ip分片
}

/* Creation primitives. */

static struct ipq *ip_frag_intern(struct ipq *qp_in) //将新创建的ipq插入到ipq散列表&lru链表中
{
	struct ipq *qp;
#ifdef CONFIG_SMP //????????????????//
	struct hlist_node *n;
#endif
	unsigned int hash;

	write_lock(&ipfrag_lock);
	hash = ipqhashfn(qp_in->id, qp_in->saddr, qp_in->daddr,
			 qp_in->protocol);
#ifdef CONFIG_SMP
	/* With SMP race we have to recheck hash table, because
	 * such entry could be created on other cpu, while we
	 * promoted read lock to write lock.
	 */
	hlist_for_each_entry(qp, n, &ipq_hash[hash], list) {
		if(qp->id == qp_in->id		&&
		   qp->saddr == qp_in->saddr	&&
		   qp->daddr == qp_in->daddr	&&
		   qp->protocol == qp_in->protocol &&
		   qp->user == qp_in->user) {
			atomic_inc(&qp->refcnt);
			write_unlock(&ipfrag_lock);
			qp_in->last_in |= COMPLETE;
			ipq_put(qp_in, NULL);
			return qp;
		}
	}
#endif
	qp = qp_in;

	if (!mod_timer(&qp->timer, jiffies + sysctl_ipfrag_time))
		atomic_inc(&qp->refcnt);

	atomic_inc(&qp->refcnt);
	hlist_add_head(&qp->list, &ipq_hash[hash]);
	INIT_LIST_HEAD(&qp->lru_list);
	list_add_tail(&qp->lru_list, &ipq_lru_list);
	ip_frag_nqueues++;
	write_unlock(&ipfrag_lock);
	return qp;
}

/* Add an entry to the 'ipq' queue for a newly received IP datagram. */
static struct ipq *ip_frag_create(struct iphdr *iph, u32 user) //每当收到一个属于新的ip数据包分片时 会创建对应的ipq 并初始化其组装超时定时器
{
	struct ipq *qp;

	if ((qp = frag_alloc_queue()) == NULL)
		goto out_nomem;

	qp->protocol = iph->protocol;
	qp->last_in = 0;
	qp->id = iph->id;
	qp->saddr = iph->saddr;
	qp->daddr = iph->daddr;
	qp->user = user;
	qp->len = 0;
	qp->meat = 0;
	qp->fragments = NULL;
	qp->iif = 0;
	qp->peer = sysctl_ipfrag_max_dist ? inet_getpeer(iph->saddr, 1) : NULL;

	/* Initialize a timer for this entry. */
	init_timer(&qp->timer);
	qp->timer.data = (unsigned long) qp;	/* pointer to queue	*/
	qp->timer.function = ip_expire;		/* expire function	*/
	spin_lock_init(&qp->lock);
	atomic_set(&qp->refcnt, 1);

	return ip_frag_intern(qp);

out_nomem:
	LIMIT_NETDEBUG(KERN_ERR "ip_frag_create: no memory left !\n");
	return NULL;
}

/* Find the correct entry in the "incomplete datagrams" queue for
 * this IP datagram, and create new one, if nothing is found.
 */
static inline struct ipq *ip_find(struct iphdr *iph, u32 user) //根据分片首部&user标志在ipq散列表中查对应ipq 未找到创建新ipq
{
	__be16 id = iph->id;
	__be32 saddr = iph->saddr;
	__be32 daddr = iph->daddr;
	__u8 protocol = iph->protocol;
	unsigned int hash;
	struct ipq *qp;
	struct hlist_node *n;

	read_lock(&ipfrag_lock);
	hash = ipqhashfn(id, saddr, daddr, protocol);
	hlist_for_each_entry(qp, n, &ipq_hash[hash], list) {
		if(qp->id == id		&&
		   qp->saddr == saddr	&&
		   qp->daddr == daddr	&&
		   qp->protocol == protocol &&
		   qp->user == user) {
			atomic_inc(&qp->refcnt);
			read_unlock(&ipfrag_lock);
			return qp;
		}
	}
	read_unlock(&ipfrag_lock);

	return ip_frag_create(iph, user);
}

/* Is the fragment too far ahead to be part of ipq? */
static inline int ip_frag_too_far(struct ipq *qp)
{
	struct inet_peer *peer = qp->peer;
	unsigned int max = sysctl_ipfrag_max_dist;
	unsigned int start, end;

	int rc;

	if (!peer || !max)
		return 0;

	start = qp->rid;
	end = atomic_inc_return(&peer->rid);
	qp->rid = end;

	rc = qp->fragments && (end - start) > max;

	if (rc) {
		IP_INC_STATS_BH(IPSTATS_MIB_REASMFAILS);
	}

	return rc;
}

static int ip_frag_reinit(struct ipq *qp)
{
	struct sk_buff *fp;

	if (!mod_timer(&qp->timer, jiffies + sysctl_ipfrag_time)) {
		atomic_inc(&qp->refcnt);
		return -ETIMEDOUT;
	}

	fp = qp->fragments;
	do {
		struct sk_buff *xp = fp->next;
		frag_kfree_skb(fp, NULL);
		fp = xp;
	} while (fp);

	qp->last_in = 0;
	qp->len = 0;
	qp->meat = 0;
	qp->fragments = NULL;
	qp->iif = 0;

	return 0;
}

/* Add new segment to existing queue. */
static void ip_frag_queue(struct ipq *qp, struct sk_buff *skb) //将分片skb添加到有qp指定的ipq分片链表中
{
	struct sk_buff *prev, *next;
	int flags, offset;
	int ihl, end;

	if (qp->last_in & COMPLETE) //分片已全部接受 则释放
		goto err;

	if (!(IPCB(skb)->flags & IPSKB_FRAG_COMPLETE) &&
	    unlikely(ip_frag_too_far(qp)) && unlikely(ip_frag_reinit(qp))) { //非本地产生的分片 调ip_frag_too_far检测分片是否存在dos攻击 是则ip_frag_reinit释放ipq所有分片
		ipq_kill(qp);
		goto err;
	}

 	offset = ntohs(skb->nh.iph->frag_off); //分别取出ip首部中的标志位 片偏移&首部长度字段 计算片偏移值和首部长度值 ip首部中的片偏移字段为13位 表示的是8字节的倍数 而首部长度字段是首部占32位字的树木
	flags = offset & ~IP_OFFSET;
	offset &= IP_OFFSET;
	offset <<= 3;		/* offset is in 8-byte chunks */
 	ihl = skb->nh.iph->ihl * 4;

	/* Determine the position of this fragment. */
 	end = offset + skb->len - ihl; //计算分片末尾处在原始数据包的位置

	/* Is this the final fragment? */
	if ((flags & IP_MF) == 0) { //如果是最后一个分片 则先对该分片进行校验: 如果其末尾小于原始包长 | ipq已有last_in标志且分片末尾不等于原始包长 则出错 通过校验后对ipq设置last_in标志 并将完整数据包长度存储在ipq的len字段中
		/* If we already have some bits beyond end
		 * or have different end, the segment is corrrupted.
		 */
		if (end < qp->len ||
		    ((qp->last_in & LAST_IN) && end != qp->len))
			goto err;
		qp->last_in |= LAST_IN;
		qp->len = end;
	} else { //不是最后一个分片 其数据长度又不8字节对齐 则将其截为8字节对齐 如果需要计算校验和 则强制设置由软件计算校验和 这是因为截断了ip有效负载 改变了长度 需重新计算校验和
		if (end&7) {
			end &= ~7;
			if (skb->ip_summed != CHECKSUM_UNNECESSARY)
				skb->ip_summed = CHECKSUM_NONE;
		}
		if (end > qp->len) { //在最后一个分片没有到达的情况下 如果当前分片的末尾在整个数据包中的位置大于ipq中len字段的值 则更新len字段 若此数据包由异常 则直接丢弃
			/* Some bits beyond end -> corruption. */ //因为ipq结构的len字段始终保持所有已接收到的分片中分片末尾在数据包中位置的最大值 而只有在收到最后一个分片后 len值才是整个数据包长度
			if (qp->last_in & LAST_IN)
				goto err;
			qp->len = end;
		}
	}
	if (end == offset) //如果分片的数据区长度为0 则该分片有异常 直接丢弃
		goto err;

	if (pskb_pull(skb, ihl) == NULL) //去掉ip首部 只保留数据部分
		goto err;
	if (pskb_trim_rcsum(skb, end-offset)) //将skb数据区长度调整为end-offset ip有效负载长度
		goto err;

	/* Find out which fragments are in front and at the back of us //确定分片在分片链表中的位置 因为各分片很可能不按顺序到达目的端 而ipq分片链表上的分片是按分片偏移值从小到大顺序链接在一起的
	 * in the chain of fragments so far.  We must know where to put
	 * this fragment, right?
	 */
	prev = NULL;
	for(next = qp->fragments; next != NULL; next = next->next) {
		if (FRAG_CB(next)->offset >= offset)
			break;	/* bingo! */
		prev = next;
	}

	/* We found where to put this one.  Check for overlap with
	 * preceding fragment, and, if needed, align things so that
	 * any overlaps are eliminated.
	 */
	if (prev) { //检测和上一个分片的数据是否有重叠 i是重叠部分数据长度 如果有重接则调pskb_pull去掉重叠部分
		int i = (FRAG_CB(prev)->offset + prev->len) - offset;

		if (i > 0) {
			offset += i;
			if (end <= offset)
				goto err;
			if (!pskb_pull(skb, i))
				goto err;
			if (skb->ip_summed != CHECKSUM_UNNECESSARY)
				skb->ip_summed = CHECKSUM_NONE;
		}
	}

	while (next && FRAG_CB(next)->offset < end) { //如果和后一个分片数据有重叠 则还需判断重叠部分的数据长度是否超过下一个分片的数据长度 没有超过则调整下一个分片 超过则需释放下一个分片后再检查与后面第二个分片的数据是否有重叠 如此反复 直到完成后面对所有分片的检查 调整分片的片偏移值 已接收分片总长度
		int i = end - FRAG_CB(next)->offset; /* overlap is 'i' bytes */

		if (i < next->len) {
			/* Eat head of the next overlapped fragment
			 * and leave the loop. The next ones cannot overlap.
			 */
			if (!pskb_pull(next, i))
				goto err;
			FRAG_CB(next)->offset += i;
			qp->meat -= i;
			if (next->ip_summed != CHECKSUM_UNNECESSARY)
				next->ip_summed = CHECKSUM_NONE;
			break;
		} else {
			struct sk_buff *free_it = next;

			/* Old fragment is completely overridden with
			 * new one drop it.
			 */
			next = next->next;

			if (prev)
				prev->next = next;
			else
				qp->fragments = next;

			qp->meat -= free_it->len;
			frag_kfree_skb(free_it, NULL);
		}
	}

	FRAG_CB(skb)->offset = offset; //记录当前分片偏移值

	/* Insert this fragment in the chain of fragments. */
	skb->next = next; //将当前分片插入到ipq分片队列中的相应位置
	if (prev)
		prev->next = skb;
	else
		qp->fragments = skb;

 	if (skb->dev)
 		qp->iif = skb->dev->ifindex;
	skb->dev = NULL;
	skb_get_timestamp(skb, &qp->stamp); //更新ipq时间戳
	qp->meat += skb->len; //累计该ipq已收到分片的总长度
	atomic_add(skb->truesize, &ip_frag_mem);  //累计分片组装模块所占内存
	if (offset == 0)
		qp->last_in |= FIRST_IN; //如果片偏移值为0 即当前分片为第一个 设置first_in标志

	write_lock(&ipfrag_lock);
	list_move_tail(&qp->lru_list, &ipq_lru_list); //调整所属ipq在ipq_lru_list链表中的位置 这是为了在占用内存超过阈值时 可先释放最近最久未使用的分片
	write_unlock(&ipfrag_lock);

	return;

err:
	kfree_skb(skb);
}


/* Build a new IP datagram from all its fragments. */

static struct sk_buff *ip_frag_reasm(struct ipq *qp, struct net_device *dev) //组装已到齐所有分片
{
	struct iphdr *iph;
	struct sk_buff *fp, *head = qp->fragments;
	int len;
	int ihlen;

	ipq_kill(qp); //将此ipq节点从ipq散列表和lrulist中摘掉 并 删除定时器

	BUG_TRAP(head != NULL);
	BUG_TRAP(FRAG_CB(head)->offset == 0);

	/* Allocate a new buffer for the datagram. */
	ihlen = head->nh.iph->ihl*4; //计算原始数据包包括ip首部的总长度 如果该长度值超过64KB则丢弃
	len = ihlen + qp->len;

	if(len > 65535) //ip数据包总长过了限值 则丢弃
		goto out_oversize;

	/* Head of list must not be cloned. */
	if (skb_cloned(head) && pskb_expand_head(head, 0, 0, GFP_ATOMIC)) //在组装分片时 所有分片都会组装到第一个分片上 因此第一个分片不能是克隆的 如果是则需为分片组装重新分配一个skb
		goto out_nomem;

	/* If the first fragment is fragmented itself, we split //分片队列的第一个skb不能既带数据有带分片 即其frag_list上不能有分片skb 如果有则重新分配一个skb 最终效果是head自身不包括数据 frag_list上连接着所有分片的skb
	 * it to two chunks: the first with data and paged part //这也是skb的一种表现形式 不一定是一个连续的数据块 但最终会调用skb_linearize将这些数据都复制到一个连续数据块中
	 * and the second, holding only fragments. */
	if (skb_shinfo(head)->frag_list) {
		struct sk_buff *clone;
		int i, plen = 0;

		if ((clone = alloc_skb(0, GFP_ATOMIC)) == NULL)
			goto out_nomem;
		clone->next = head->next;
		head->next = clone;
		skb_shinfo(clone)->frag_list = skb_shinfo(head)->frag_list;
		skb_shinfo(head)->frag_list = NULL;
		for (i=0; i<skb_shinfo(head)->nr_frags; i++)
			plen += skb_shinfo(head)->frags[i].size;
		clone->len = clone->data_len = head->data_len - plen;
		head->data_len -= clone->len;
		head->len -= clone->len;
		clone->csum = 0;
		clone->ip_summed = head->ip_summed;
		atomic_add(clone->truesize, &ip_frag_mem);
	}

	skb_shinfo(head)->frag_list = head->next; //把所有分片组装起来即将分片链到第一个skb的frag_list上 同时还需要遍历所有分片 重新计算ip数据包长度&校验和
	skb_push(head, head->data - head->nh.raw);
	atomic_sub(head->truesize, &ip_frag_mem);

	for (fp=head->next; fp; fp = fp->next) {
		head->data_len += fp->len;
		head->len += fp->len;
		if (head->ip_summed != fp->ip_summed)
			head->ip_summed = CHECKSUM_NONE;
		else if (head->ip_summed == CHECKSUM_COMPLETE)
			head->csum = csum_add(head->csum, fp->csum);
		head->truesize += fp->truesize;
		atomic_sub(fp->truesize, &ip_frag_mem);
	}

	head->next = NULL;
	head->dev = dev;
	skb_set_timestamp(head, &qp->stamp);

	iph = head->nh.iph; //重置首部长度 片偏移 标志位 和 总长度
	iph->frag_off = 0;
	iph->tot_len = htons(len);
	IP_INC_STATS_BH(IPSTATS_MIB_REASMOKS);
	qp->fragments = NULL; //既然各分片都已处理好 释放ipq的分片队列
	return head;

out_nomem:
 	LIMIT_NETDEBUG(KERN_ERR "IP: queue_glue: no memory for gluing "
			      "queue %p\n", qp);
	goto out_fail;
out_oversize:
	if (net_ratelimit())
		printk(KERN_INFO
			"Oversized IP packet from %d.%d.%d.%d.\n",
			NIPQUAD(qp->saddr));
out_fail:
	IP_INC_STATS_BH(IPSTATS_MIB_REASMFAILS);
	return NULL;
}

/* Process an incoming IP datagram fragment. */
struct sk_buff *ip_defrag(struct sk_buff *skb, u32 user) //ip组装有三剑客:
{                                                        //首先判断接收到的ip数据包是否是一个分片 如果是则在传递给上层协议前 需先分片组装
	struct iphdr *iph = skb->nh.iph;                     //以(daddr saddr protocol id ipfrag_hash_md)计算键值 在ipq散列表中找到分片所属ipq 并按序插入到该ipq分片链表中
	struct ipq *qp;                                      //如果此时该ipq的所有分片已经全部到达 则将这些分片组装成一个完整的ip数据包
	struct net_device *dev;
	
	IP_INC_STATS_BH(IPSTATS_MIB_REASMREQDS); //统计mib的ipstats_mib_reasmreqds数据

	/* Start by cleaning up the memory. */
	if (atomic_read(&ip_frag_mem) > sysctl_ipfrag_high_thresh) //如果ipq散列表消耗的内存大于指定值时 需调ip_evictor清理分片
		ip_evictor();

	dev = skb->dev; //获取接收数据包的网络设备指针

	/* Lookup (or create) queue header */
	if ((qp = ip_find(iph, user)) != NULL) { //调用ipfind在 ipq散列表中查找分片所属ipq 如果找不到则创建一个新的ipq 如果返回值为NULL 则说明查找及创建均失败
		struct sk_buff *ret = NULL;

		spin_lock(&qp->lock);

		ip_frag_queue(qp, skb); //将分片插入到ipq分片链表适当位置

		if (qp->last_in == (FIRST_IN|LAST_IN) &&  //当该ipq的第一个分片和最后一个分片都已收到 &如果已经接受数据包总长度与原始数据包长度相等 则说明该原始数据包的所有分片都已到齐 则调ip_frag_reasm组装分片
		    qp->meat == qp->len)
			ret = ip_frag_reasm(qp, dev);

		spin_unlock(&qp->lock);
		ipq_put(qp, NULL); //删除ipq及其所有分片
		return ret;
	}

	IP_INC_STATS_BH(IPSTATS_MIB_REASMFAILS); //统计mib的ipstats_mib_reasmfails数据
	kfree_skb(skb); //释放分片
	return NULL;
}

void ipfrag_init(void)
{
	ipfrag_hash_rnd = (u32) ((num_physpages ^ (num_physpages>>7)) ^
				 (jiffies ^ (jiffies >> 6)));

	init_timer(&ipfrag_secret_timer); //ipq散列表的定时重组是通过ipfrag_secret_timer定时器实现的 这里是初始化定时器
	ipfrag_secret_timer.function = ipfrag_secret_rebuild;
	ipfrag_secret_timer.expires = jiffies + sysctl_ipfrag_secret_interval; //10min
	add_timer(&ipfrag_secret_timer);
}

EXPORT_SYMBOL(ip_defrag);

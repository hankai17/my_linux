/*
 * net/sched/sch_generic.c	Generic packet scheduler routines.
 *
 *		This program is free software; you can redistribute it and/or
 *		modify it under the terms of the GNU General Public License
 *		as published by the Free Software Foundation; either version
 *		2 of the License, or (at your option) any later version.
 *
 * Authors:	Alexey Kuznetsov, <kuznet@ms2.inr.ac.ru>
 *              Jamal Hadi Salim, <hadi@cyberus.ca> 990601
 *              - Ingress support
 */

#include <asm/uaccess.h>
#include <asm/system.h>
#include <linux/bitops.h>
#include <linux/module.h>
#include <linux/types.h>
#include <linux/kernel.h>
#include <linux/sched.h>
#include <linux/string.h>
#include <linux/mm.h>
#include <linux/socket.h>
#include <linux/sockios.h>
#include <linux/in.h>
#include <linux/errno.h>
#include <linux/interrupt.h>
#include <linux/netdevice.h>
#include <linux/skbuff.h>
#include <linux/rtnetlink.h>
#include <linux/init.h>
#include <linux/rcupdate.h>
#include <linux/list.h>
#include <net/sock.h>
#include <net/pkt_sched.h>

/* Main transmission queue. */

/* Main qdisc structure lock. 

   However, modifications
   to data, participating in scheduling must be additionally
   protected with dev->queue_lock spinlock.

   The idea is the following:
   - enqueue, dequeue are serialized via top level device
     spinlock dev->queue_lock.
   - tree walking is protected by read_lock(qdisc_tree_lock)
     and this lock is used only in process context.
   - updates to tree are made only under rtnl semaphore,
     hence this lock may be made without local bh disabling.

   qdisc_tree_lock must be grabbed BEFORE dev->queue_lock!
 */
DEFINE_RWLOCK(qdisc_tree_lock);

void qdisc_lock_tree(struct net_device *dev)
{
	write_lock(&qdisc_tree_lock);
	spin_lock_bh(&dev->queue_lock);
}

void qdisc_unlock_tree(struct net_device *dev)
{
	spin_unlock_bh(&dev->queue_lock);
	write_unlock(&qdisc_tree_lock);
}

/* 
   dev->queue_lock serializes queue accesses for this device
   AND dev->qdisc pointer itself.

   netif_tx_lock serializes accesses to device driver.

   dev->queue_lock and netif_tx_lock are mutually exclusive,
   if one is grabbed, another must be free.
 */


/* Kick device.
   Note, that this procedure can be called by a watchdog timer, so that
   we do not check dev->tbusy flag here.

   Returns:  0  - queue is empty.
            >0  - queue is not empty, but throttled.
	    <0  - queue is not empty. Device is throttled, if dev->tbusy != 0.

   NOTE: Called under dev->queue_lock with locally disabled BH.
*/

static inline int qdisc_restart(struct net_device *dev) //从排队规则中获取一个可以输出的报文 然后将其输出到网卡
{
	struct Qdisc *q = dev->qdisc;
	struct sk_buff *skb;

	/* Dequeue packet */
	if (((skb = dev->gso_skb)) || ((skb = q->dequeue(q)))) { //如果还有上次没发送完的GSO包 则将其取出 开始进行输出 同时获取网卡输出数据包时 是否需要上锁标志    //从排队规则队列中取出待输出的数据包  //这个|用的真好!!!
		unsigned nolock = (dev->features & NETIF_F_LLTX);

		dev->gso_skb = NULL; //无论输出的是否是缓存的GSO包 都要将输出网卡上用于缓存GSO数据包的指针清零 如果本次输出后 还有未发送完的GSO包则重置该指针

		/*
		 * When the driver has LLTX set it does its own locking
		 * in start_xmit. No need to add additional overhead by
		 * locking again. These checks are worth it because
		 * even uncongested locks can be quite expensive.
		 * The driver can do trylock like here too, in case
		 * of lock congestion it should return -1 and the packet
		 * will be requeued.
		 */
		if (!nolock) {
			if (!netif_tx_trylock(dev)) { //如果输出网卡设置了输出数据包时 需要上锁 则加锁 若失败 做相应处理: 如果正在通过该网卡发送数据包的cpu是当前cpu 则说明代码有bug 需要释放待输出的数据包 其他情况: 比如其他cpu的锁定等 则统计相应数据后 将报文缓存起来或重新排入队列
			collision: //代码有bug | 其他cpu锁定而需等待
				/* So, someone grabbed the driver. */
				
				/* It may be transient configuration error,
				   when hard_start_xmit() recurses. We detect
				   it by checking xmit owner and drop the
				   packet when deadloop is detected.
				*/
				if (dev->xmit_lock_owner == smp_processor_id()) {
					kfree_skb(skb);
					if (net_ratelimit())
						printk(KERN_DEBUG "Dead loop on netdevice %s, fix it urgently!\n", dev->name);
					return -1;
				}
				__get_cpu_var(netdev_rx_stat).cpu_collision++;
				goto requeue;
			}
		}
		
		{
			/* And release queue */
			spin_unlock(&dev->queue_lock);

			if (!netif_queue_stopped(dev)) { //检测网卡是否关闭了排队功能 如果处于启用态 则调用dev_hard_start_xmit将数据包从输出网卡中输出 成功则反-1 表示队列中仍有数据待发
				int ret;

				ret = dev_hard_start_xmit(skb, dev);
				if (ret == NETDEV_TX_OK) { 
					if (!nolock) {
						netif_tx_unlock(dev);
					}
					spin_lock(&dev->queue_lock);
					return -1;
				}
				if (ret == NETDEV_TX_LOCKED && nolock) { //如果由于输出锁已上锁而发送失败 & 输出数据包时无需上锁 则跳到collision
					spin_lock(&dev->queue_lock);
					goto collision; 
				}
			}

			/* NETDEV_TX_BUSY - we need to requeue */
			/* Release the driver */
			if (!nolock) {  //由于缓存不够 网卡硬件错误 等原因而关闭排队功能 则获取网卡当前使用的排队规则
				netif_tx_unlock(dev);
			} 
			spin_lock(&dev->queue_lock);
			q = dev->qdisc;
		}

		/* Device kicked us out :(
		   This is possible in three cases:

		   0. driver is locked
		   1. fastroute is enabled
		   2. device cannot determine busy state
		      before start of transmission (f.e. dialout)
		   3. device is buggy (ppp)
		 */

requeue:
		if (skb->next) //将由于其他cpu上锁而无法输出的GSO数据包缓存到输出网卡上 而其他数据包则重新排入队列 然后再次调度数据包输出软中断 进行下一次数据包输出 反1表示队列还有数据包 但由于上锁失败而等待发送
			dev->gso_skb = skb;
		else
			q->ops->requeue(skb, q);
		netif_schedule(dev);
		return 1;
	}
	BUG_ON((int) q->q.qlen < 0);
	return q->q.qlen; //如果出队失败 即队列中没有数据包 | 本次没有数据包需要输出 直接反出队列中的数据包数
}

void __qdisc_run(struct net_device *dev)
{
	if (unlikely(dev->qdisc == &noop_qdisc)) //如果输出网络设备的排队规则还处于初始化态 则没必要调度数据包输出软中断 退出流控调度队列过程态
		goto out;

	while (qdisc_restart(dev) < 0 && !netif_queue_stopped(dev)) //qdisc_restart进行发送 直到发送完毕或网卡为停止态
		/* NOTHING */;

out:
	clear_bit(__LINK_STATE_QDISC_RUNNING, &dev->state); //如果没有输出流控  则退出
}

static void dev_watchdog(unsigned long arg)
{
	struct net_device *dev = (struct net_device *)arg;

	netif_tx_lock(dev);
	if (dev->qdisc != &noop_qdisc) {
		if (netif_device_present(dev) &&
		    netif_running(dev) &&
		    netif_carrier_ok(dev)) {
			if (netif_queue_stopped(dev) &&
			    time_after(jiffies, dev->trans_start + dev->watchdog_timeo)) {

				printk(KERN_INFO "NETDEV WATCHDOG: %s: transmit timed out\n",
				       dev->name);
				dev->tx_timeout(dev);
			}
			if (!mod_timer(&dev->watchdog_timer, jiffies + dev->watchdog_timeo))
				dev_hold(dev);
		}
	}
	netif_tx_unlock(dev);

	dev_put(dev);
}

static void dev_watchdog_init(struct net_device *dev)
{
	init_timer(&dev->watchdog_timer);
	dev->watchdog_timer.data = (unsigned long)dev;
	dev->watchdog_timer.function = dev_watchdog;
}

void __netdev_watchdog_up(struct net_device *dev)
{
	if (dev->tx_timeout) {
		if (dev->watchdog_timeo <= 0)
			dev->watchdog_timeo = 5*HZ;
		if (!mod_timer(&dev->watchdog_timer, jiffies + dev->watchdog_timeo))
			dev_hold(dev);
	}
}

static void dev_watchdog_up(struct net_device *dev)
{
	__netdev_watchdog_up(dev);
}

static void dev_watchdog_down(struct net_device *dev)
{
	netif_tx_lock_bh(dev);
	if (del_timer(&dev->watchdog_timer))
		dev_put(dev);
	netif_tx_unlock_bh(dev);
}

void netif_carrier_on(struct net_device *dev)
{
	if (test_and_clear_bit(__LINK_STATE_NOCARRIER, &dev->state))
		linkwatch_fire_event(dev);
	if (netif_running(dev))
		__netdev_watchdog_up(dev);
}

void netif_carrier_off(struct net_device *dev)
{
	if (!test_and_set_bit(__LINK_STATE_NOCARRIER, &dev->state))
		linkwatch_fire_event(dev);
}

/* "NOOP" scheduler: the best scheduler, recommended for all interfaces
   under all circumstances. It is difficult to invent anything faster or
   cheaper.
 */

static int noop_enqueue(struct sk_buff *skb, struct Qdisc * qdisc)
{
	kfree_skb(skb);
	return NET_XMIT_CN;
}

static struct sk_buff *noop_dequeue(struct Qdisc * qdisc)
{
	return NULL;
}

static int noop_requeue(struct sk_buff *skb, struct Qdisc* qdisc)
{
	if (net_ratelimit())
		printk(KERN_DEBUG "%s deferred output. It is buggy.\n",
		       skb->dev->name);
	kfree_skb(skb);
	return NET_XMIT_CN;
}

struct Qdisc_ops noop_qdisc_ops = {
	.id		=	"noop",
	.priv_size	=	0,
	.enqueue	=	noop_enqueue,
	.dequeue	=	noop_dequeue,
	.requeue	=	noop_requeue,
	.owner		=	THIS_MODULE,
};

struct Qdisc noop_qdisc = {
	.enqueue	=	noop_enqueue,
	.dequeue	=	noop_dequeue,
	.flags		=	TCQ_F_BUILTIN,
	.ops		=	&noop_qdisc_ops,	
	.list		=	LIST_HEAD_INIT(noop_qdisc.list),
};

static struct Qdisc_ops noqueue_qdisc_ops = {
	.id		=	"noqueue",
	.priv_size	=	0,
	.enqueue	=	noop_enqueue,
	.dequeue	=	noop_dequeue,
	.requeue	=	noop_requeue,
	.owner		=	THIS_MODULE,
};

static struct Qdisc noqueue_qdisc = {
	.enqueue	=	NULL,
	.dequeue	=	noop_dequeue,
	.flags		=	TCQ_F_BUILTIN,
	.ops		=	&noqueue_qdisc_ops,
	.list		=	LIST_HEAD_INIT(noqueue_qdisc.list),
};


static const u8 prio2band[TC_PRIO_MAX+1] =
	{ 1, 2, 2, 2, 1, 2, 0, 0 , 1, 1, 1, 1, 1, 1, 1, 1 };

/* 3-band FIFO queue: old style, but should be a bit faster than
   generic prio+fifo combination.
 */

#define PFIFO_FAST_BANDS 3

static inline struct sk_buff_head *prio2list(struct sk_buff *skb,
					     struct Qdisc *qdisc)
{
	struct sk_buff_head *list = qdisc_priv(qdisc);
	return list + prio2band[skb->priority & TC_PRIO_MAX];
}

static int pfifo_fast_enqueue(struct sk_buff *skb, struct Qdisc* qdisc) //根据数据包的优先级 将其加入到对应的队列中
{
	struct sk_buff_head *list = prio2list(skb, qdisc);

	if (skb_queue_len(list) < qdisc->dev->tx_queue_len) { //如果队列中的数据包未到上限 则将数据包排到对应优先级队列尾部 如果到了上限则丢弃待入队的数据包
		qdisc->q.qlen++;
		return __qdisc_enqueue_tail(skb, qdisc, list);
	}

	return qdisc_drop(skb, qdisc);
}

static struct sk_buff *pfifo_fast_dequeue(struct Qdisc* qdisc)
{
	int prio;
	struct sk_buff_head *list = qdisc_priv(qdisc);

	for (prio = 0; prio < PFIFO_FAST_BANDS; prio++) { //一旦取到一个数据包就反出 只有优先级队列未空时 才从下一优先级队列中获取数据包
		if (!skb_queue_empty(list + prio)) {
			qdisc->q.qlen--;
			return __qdisc_dequeue_head(qdisc, list + prio);
		}
	}

	return NULL;
}

static int pfifo_fast_requeue(struct sk_buff *skb, struct Qdisc* qdisc) //当报文由于发送而出队 但又因为某个不可预见的原因没有发出去时 得将这个数据包重新入队 等下次发送
{
	qdisc->q.qlen++;
	return __qdisc_requeue(skb, qdisc, prio2list(skb, qdisc));
}

static void pfifo_fast_reset(struct Qdisc* qdisc)
{
	int prio;
	struct sk_buff_head *list = qdisc_priv(qdisc);

	for (prio = 0; prio < PFIFO_FAST_BANDS; prio++)
		__qdisc_reset_queue(qdisc, list + prio);

	qdisc->qstats.backlog = 0;
	qdisc->q.qlen = 0;
}

static int pfifo_fast_dump(struct Qdisc *qdisc, struct sk_buff *skb)
{
	struct tc_prio_qopt opt = { .bands = PFIFO_FAST_BANDS };

	memcpy(&opt.priomap, prio2band, TC_PRIO_MAX+1);
	RTA_PUT(skb, TCA_OPTIONS, sizeof(opt), &opt);
	return skb->len;

rtattr_failure:
	return -1;
}

static int pfifo_fast_init(struct Qdisc *qdisc, struct rtattr *opt) //fifo规则之所以简单是因为没有类和过滤器
{
	int prio;
	struct sk_buff_head *list = qdisc_priv(qdisc);

	for (prio = 0; prio < PFIFO_FAST_BANDS; prio++) //pfifo内部有三个优先级队列
		skb_queue_head_init(list + prio);

	return 0;
}

static struct Qdisc_ops pfifo_fast_ops = {
	.id		=	"pfifo_fast",
	.priv_size	=	PFIFO_FAST_BANDS * sizeof(struct sk_buff_head),
	.enqueue	=	pfifo_fast_enqueue,
	.dequeue	=	pfifo_fast_dequeue,
	.requeue	=	pfifo_fast_requeue,
	.init		=	pfifo_fast_init,
	.reset		=	pfifo_fast_reset,
	.dump		=	pfifo_fast_dump,
	.owner		=	THIS_MODULE,
};

struct Qdisc *qdisc_alloc(struct net_device *dev, struct Qdisc_ops *ops)
{
	void *p;
	struct Qdisc *sch;
	unsigned int size;
	int err = -ENOBUFS;

	/* ensure that the Qdisc and the private data are 32-byte aligned */
	size = QDISC_ALIGN(sizeof(*sch));
	size += ops->priv_size + (QDISC_ALIGNTO - 1);

	p = kzalloc(size, GFP_KERNEL);
	if (!p)
		goto errout;
	sch = (struct Qdisc *) QDISC_ALIGN((unsigned long) p);
	sch->padded = (char *) sch - (char *) p;

	INIT_LIST_HEAD(&sch->list);
	skb_queue_head_init(&sch->q);
	sch->ops = ops;
	sch->enqueue = ops->enqueue;
	sch->dequeue = ops->dequeue;
	sch->dev = dev;
	dev_hold(dev);
	sch->stats_lock = &dev->queue_lock;
	atomic_set(&sch->refcnt, 1);

	return sch;
errout:
	return ERR_PTR(-err);
}

struct Qdisc * qdisc_create_dflt(struct net_device *dev, struct Qdisc_ops *ops,
				 unsigned int parentid)
{
	struct Qdisc *sch;
	
	sch = qdisc_alloc(dev, ops);
	if (IS_ERR(sch))
		goto errout;
	sch->parent = parentid;

	if (!ops->init || ops->init(sch, NULL) == 0)
		return sch;

	qdisc_destroy(sch);
errout:
	return NULL;
}

/* Under dev->queue_lock and BH! */

void qdisc_reset(struct Qdisc *qdisc)
{
	struct Qdisc_ops *ops = qdisc->ops;

	if (ops->reset)
		ops->reset(qdisc);
}

/* this is the rcu callback function to clean up a qdisc when there 
 * are no further references to it */

static void __qdisc_destroy(struct rcu_head *head)
{
	struct Qdisc *qdisc = container_of(head, struct Qdisc, q_rcu);
	kfree((char *) qdisc - qdisc->padded);
}

/* Under dev->queue_lock and BH! */

void qdisc_destroy(struct Qdisc *qdisc)
{
	struct Qdisc_ops  *ops = qdisc->ops;

	if (qdisc->flags & TCQ_F_BUILTIN ||
	    !atomic_dec_and_test(&qdisc->refcnt))
		return;

	list_del(&qdisc->list);
#ifdef CONFIG_NET_ESTIMATOR
	gen_kill_estimator(&qdisc->bstats, &qdisc->rate_est);
#endif
	if (ops->reset)
		ops->reset(qdisc);
	if (ops->destroy)
		ops->destroy(qdisc);

	module_put(ops->owner);
	dev_put(qdisc->dev);
	call_rcu(&qdisc->q_rcu, __qdisc_destroy);
}

void dev_activate(struct net_device *dev) //初始化流控排队规则 & 启动监视定时器  默认流控为FIFO
{
	/* No queueing discipline is attached to device;
	   create default one i.e. pfifo_fast for devices,
	   which need queueing and noqueue_qdisc for
	   virtual interfaces
	 */

	if (dev->qdisc_sleeping == &noop_qdisc) { //如果网卡当前没有安装有效的排队规则 则需安装默认的排队规则(pfifo noqueue) pfifo需根据网卡支持的发送队列最大帧数设置  noqueue没有enqueue接口 当dev_queue_xmit输出报文时 发现不支持enqueue接口 就直接发送报文 不用排队
		struct Qdisc *qdisc;
		if (dev->tx_queue_len) {
			qdisc = qdisc_create_dflt(dev, &pfifo_fast_ops,
						  TC_H_ROOT);
			if (qdisc == NULL) {
				printk(KERN_INFO "%s: activation failed\n", dev->name);
				return;
			}
			write_lock(&qdisc_tree_lock);
			list_add_tail(&qdisc->list, &dev->qdisc_list);
			write_unlock(&qdisc_tree_lock);
		} else {
			qdisc =  &noqueue_qdisc;
		}
		write_lock(&qdisc_tree_lock);
		dev->qdisc_sleeping = qdisc;
		write_unlock(&qdisc_tree_lock);
	}

	if (!netif_carrier_ok(dev)) //检测网卡是否处于可传递包态 不是则延迟应用已安装的排队规则 直到转变为可传递数据包态
		/* Delay activation until next carrier-on event */
		return;

	spin_lock_bh(&dev->queue_lock);
	rcu_assign_pointer(dev->qdisc, dev->qdisc_sleeping);
	if (dev->qdisc != &noqueue_qdisc) { //处于可传递数据包态 则应用已安装的排队规则 & 打开网卡看门狗 监视报文发送是否超时
		dev->trans_start = jiffies;
		dev_watchdog_up(dev);
	}
	spin_unlock_bh(&dev->queue_lock);
}

void dev_deactivate(struct net_device *dev) //禁止出口队列规则 确保该设备不在用于传输 & 停止监控定时器 将网络设备置位禁止传递数据包态
{
	struct Qdisc *qdisc;

	spin_lock_bh(&dev->queue_lock);
	qdisc = dev->qdisc;
	dev->qdisc = &noop_qdisc; //将网卡排队规则置空 & 重新初始化排队规则

	qdisc_reset(qdisc);

	spin_unlock_bh(&dev->queue_lock);

	dev_watchdog_down(dev); //关闭网卡看门狗 停止监视报文发送是否超时

	/* Wait for outstanding dev_queue_xmit calls. */
	synchronize_rcu(); //暂时让出处理器而阻塞 唤醒dev_queue_xmit的执行进程 完成dev_queue_xmit的调用

	/* Wait for outstanding qdisc_run calls. */
	while (test_bit(__LINK_STATE_QDISC_RUNNING, &dev->state)) //如果网卡还在进行流控角度队列过程中 尽量让出处理器 尽可能完成qdisc_run的调用
		yield();

	if (dev->gso_skb) { //最后如果网卡上还有缓存GSO报文 将其释放
		kfree_skb(dev->gso_skb);
		dev->gso_skb = NULL;
	}
}

void dev_init_scheduler(struct net_device *dev) //dev_init_scheduler
{
	qdisc_lock_tree(dev);
	dev->qdisc = &noop_qdisc; //noop_ 即对数据包不进行任何分类或排队 而直接丢弃 因为还处于register阶段 网卡还不能发送任何数据包
	dev->qdisc_sleeping = &noop_qdisc;
	INIT_LIST_HEAD(&dev->qdisc_list);
	qdisc_unlock_tree(dev);

	dev_watchdog_init(dev);
}

void dev_shutdown(struct net_device *dev)
{
	struct Qdisc *qdisc;

	qdisc_lock_tree(dev);
	qdisc = dev->qdisc_sleeping;
	dev->qdisc = &noop_qdisc;
	dev->qdisc_sleeping = &noop_qdisc;
	qdisc_destroy(qdisc);
#if defined(CONFIG_NET_SCH_INGRESS) || defined(CONFIG_NET_SCH_INGRESS_MODULE)
        if ((qdisc = dev->qdisc_ingress) != NULL) {
		dev->qdisc_ingress = NULL;
		qdisc_destroy(qdisc);
        }
#endif
	BUG_TRAP(!timer_pending(&dev->watchdog_timer));
	qdisc_unlock_tree(dev);
}

EXPORT_SYMBOL(netif_carrier_on);
EXPORT_SYMBOL(netif_carrier_off);
EXPORT_SYMBOL(noop_qdisc);
EXPORT_SYMBOL(qdisc_create_dflt);
EXPORT_SYMBOL(qdisc_destroy);
EXPORT_SYMBOL(qdisc_reset);
EXPORT_SYMBOL(qdisc_lock_tree);
EXPORT_SYMBOL(qdisc_unlock_tree);

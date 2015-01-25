/*-
 * Copyright (c) 2004-2010 University of Zagreb
 * Copyright (c) 2007-2008 FreeBSD Foundation
 * Copyright (c) 2014 Dmitry Petuhov <mityapetuhov@gmail.com>
 *
 * This software was developed by the University of Zagreb and the
 * FreeBSD Foundation under sponsorship by the Stichting NLnet and the
 * FreeBSD Foundation.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

/*
 * This node permits simple traffic shaping by emulating bandwidth.
 * The node has two hooks, upper and lower. Traffic flowing from upper to
 * lower hook is referenced as downstream, and vice versa. Parameters for
 * both directions can be set separately.
 */

/* temporary for debug */
//#define NETGRAPH_DEBUG 1
#include <sys/syslog.h>

#include <sys/param.h>
#include <sys/errno.h>
#include <sys/kernel.h>
#include <sys/malloc.h>
#include <sys/mbuf.h>
#include <sys/time.h>
#include <sys/fnv_hash.h>

#include <vm/uma.h>

#include <netinet/in.h>
#include <netinet/ip.h>
#include <netinet/ip6.h>
#include <net/ethernet.h>

#include <netgraph/ng_message.h>
#include <netgraph/netgraph.h>
#include <netgraph/ng_parse.h>
#include <ng_pipe_lt.h>

static MALLOC_DEFINE(M_NG_PIPE_LT, "ng_pipe_lt", "ng_pipe_lt");
/* From in_var.h */
#define INADDR_HASHVAL(x)	fnv_32_buf((&(x)), sizeof(x), FNV1_32_INIT)
/* From in6_var.h */
static __inline uint32_t
in6_addrhash(struct in6_addr *in6)
{
        uint32_t x;

        x = in6->s6_addr32[0] ^ in6->s6_addr32[1] ^ in6->s6_addr32[2] ^
            in6->s6_addr32[3];
        return (fnv_32_buf(&x, sizeof(x), FNV1_32_INIT));
}
#define IN6ADDR_HASHVAL(x)	(in6_addrhash(x))

#define NGPL_QUEUES	32

/* Packet header struct */
struct ngpl_hdr {
	TAILQ_ENTRY(ngpl_hdr)	ngpl_link;	/* next pkt in queue */
	item_p			item;		/* ptr to netgraph internal decriptor */
	struct mbuf		*m;		/* ptr to the packet data */
};
TAILQ_HEAD(p_head, ngpl_hdr);

/* FIFO queue struct */
struct ngpl_fifo {
	TAILQ_ENTRY(ngpl_fifo)	fifo_le;	/* list of active queues only */
	struct p_head		packet_head;	/* FIFO queue head */
	u_int32_t		hash;		/* flow signature */
	u_int32_t		rr_deficit;	/* for DRR */
	u_int32_t		packets;	/* # of packets in this queue */
};

/* Per hook info */
struct hookinfo {
	hook_p			hook;
	int			noqueue;	/* bypass any processing */
	TAILQ_HEAD(, ngpl_fifo)	fifo_head;	/* FIFO queues */
	struct ngpl_fifo 	*fifo_array[NGPL_QUEUES]; /* array of same FIFO queues */
	struct ngpl_fifo	*ackq;		/* Separate queue for TCK ACKs */
	struct ng_pipe_hookcfg	cfg;
	struct ng_pipe_hookrun	run;
	struct ng_pipe_hookstat	stats;
	struct timeval          last_refill;    /* time of last refill */
};

/* Per node info */
struct node_priv {
	struct hookinfo		lower;
	struct hookinfo		upper;
	struct callout		timer;
	int			timer_scheduled;
};
typedef struct node_priv *priv_p;

static void	parse_cfg(struct ng_pipe_hookcfg *, struct ng_pipe_hookcfg *,
			struct hookinfo *, priv_p);
static void	pipe_dequeue(struct hookinfo *, struct timeval *);
static void	ngpl_callout(node_p, hook_p, void *, int);
static int	ngpl_modevent(module_t, int, void *);

/* zones for storing ngpl_hdr-s and ngpl_fifo-s*/
static uma_zone_t ngpl_zone_hdr;
static uma_zone_t ngpl_zone_fifo;

/* Netgraph methods */
static ng_constructor_t	ngpl_constructor;
static ng_rcvmsg_t	ngpl_rcvmsg;
static ng_shutdown_t	ngpl_shutdown;
static ng_newhook_t	ngpl_newhook;
static ng_rcvdata_t	ngpl_rcvdata;
static ng_disconnect_t	ngpl_disconnect;

/* Parse type for struct ng_pipe_hookstat */
static const struct ng_parse_struct_field
	ng_pipe_hookstat_type_fields[] = NG_PIPE_HOOKSTAT_INFO;
static const struct ng_parse_type ng_pipe_hookstat_type = {
	&ng_parse_struct_type,
	&ng_pipe_hookstat_type_fields
};

/* Parse type for struct ng_pipe_stats */
static const struct ng_parse_struct_field ng_pipe_stats_type_fields[] =
	NG_PIPE_STATS_INFO(&ng_pipe_hookstat_type);
static const struct ng_parse_type ng_pipe_stats_type = {
	&ng_parse_struct_type,
	&ng_pipe_stats_type_fields
};

/* Parse type for struct ng_pipe_hookrun */
static const struct ng_parse_struct_field
	ng_pipe_hookrun_type_fields[] = NG_PIPE_HOOKRUN_INFO;
static const struct ng_parse_type ng_pipe_hookrun_type = {
	&ng_parse_struct_type,
	&ng_pipe_hookrun_type_fields
};

/* Parse type for struct ng_pipe_run */
static const struct ng_parse_struct_field
	ng_pipe_run_type_fields[] = NG_PIPE_RUN_INFO(&ng_pipe_hookrun_type);
static const struct ng_parse_type ng_pipe_run_type = {
	&ng_parse_struct_type,
	&ng_pipe_run_type_fields
};

/* Parse type for struct ng_pipe_hookcfg */
static const struct ng_parse_struct_field
	ng_pipe_hookcfg_type_fields[] = NG_PIPE_HOOKCFG_INFO;
static const struct ng_parse_type ng_pipe_hookcfg_type = {
	&ng_parse_struct_type,
	&ng_pipe_hookcfg_type_fields
};

/* Parse type for struct ng_pipe_cfg */
static const struct ng_parse_struct_field
	ng_pipe_cfg_type_fields[] = NG_PIPE_CFG_INFO(&ng_pipe_hookcfg_type);
static const struct ng_parse_type ng_pipe_cfg_type = {
	&ng_parse_struct_type,
	&ng_pipe_cfg_type_fields
};

/* List of commands and how to convert arguments to/from ASCII */
static const struct ng_cmdlist ngpl_cmds[] = {
	{
		.cookie =	NGM_PIPE_COOKIE,
		.cmd =		NGM_PIPE_GET_STATS,
		.name = 	"getstats",
		.respType =	 &ng_pipe_stats_type
	},
	{
		.cookie =	NGM_PIPE_COOKIE,
		.cmd =		NGM_PIPE_CLR_STATS,
		.name =		"clrstats"
	},
	{
		.cookie =	NGM_PIPE_COOKIE,
		.cmd =		NGM_PIPE_GETCLR_STATS,
		.name =		"getclrstats",
		.respType =	&ng_pipe_stats_type
	},
	{
		.cookie =	NGM_PIPE_COOKIE,
		.cmd =		NGM_PIPE_GET_RUN,
		.name =		"getrun",
		.respType =	&ng_pipe_run_type
	},
	{
		.cookie =	NGM_PIPE_COOKIE,
		.cmd =		NGM_PIPE_GET_CFG,
		.name =		"getcfg",
		.respType =	&ng_pipe_cfg_type
	},
	{
		.cookie =	NGM_PIPE_COOKIE,
		.cmd =		NGM_PIPE_SET_CFG,
		.name =		"setcfg",
		.mesgType =	&ng_pipe_cfg_type,
	},
	{ 0 }
};

/* Netgraph type descriptor */
static struct ng_type ng_pipe_typestruct = {
	.version =	NG_ABI_VERSION,
	.name =		NG_PIPE_NODE_TYPE,
	.mod_event =	ngpl_modevent,
	.constructor =	ngpl_constructor,
	.shutdown =	ngpl_shutdown,
	.rcvmsg =	ngpl_rcvmsg,
	.newhook =	ngpl_newhook,
	.rcvdata =	ngpl_rcvdata,
	.disconnect =	ngpl_disconnect,
	.cmdlist =	ngpl_cmds
};
NETGRAPH_INIT(pipe_lt, &ng_pipe_typestruct);

/* Node constructor */
static int
ngpl_constructor(node_p node)
{
	priv_p priv;

	priv = malloc(sizeof(*priv), M_NG_PIPE_LT, M_ZERO | M_WAITOK);
	NG_NODE_SET_PRIVATE(node, priv);

	/* Mark node as single-threaded */
	NG_NODE_FORCE_WRITER(node);

	ng_callout_init(&priv->timer);

	return (0);
}

/* Add a hook */
static int
ngpl_newhook(node_p node, hook_p hook, const char *name)
{
	const priv_p priv = NG_NODE_PRIVATE(node);
	struct hookinfo *hinfo;

	if (strcmp(name, NG_PIPE_HOOK_UPPER) == 0) {
		bzero(&priv->upper, sizeof(priv->upper));
		priv->upper.hook = hook;
		NG_HOOK_SET_PRIVATE(hook, &priv->upper);
	} else if (strcmp(name, NG_PIPE_HOOK_LOWER) == 0) {
		bzero(&priv->lower, sizeof(priv->lower));
		priv->lower.hook = hook;
		NG_HOOK_SET_PRIVATE(hook, &priv->lower);
	} else
		return (EINVAL);

	/* Load non-zero initial cfg values */
	hinfo = NG_HOOK_PRIVATE(hook);
	hinfo->cfg.qin_size_limit = 100;
	hinfo->cfg.fifo = 1;
	TAILQ_INIT(&hinfo->fifo_head);
	return (0);
}

/* Receive a control message */
static int
ngpl_rcvmsg(node_p node, item_p item, hook_p lasthook)
{
	const priv_p priv = NG_NODE_PRIVATE(node);
	struct ng_mesg *resp = NULL;
	struct ng_mesg *msg;
	struct ng_pipe_stats *stats;
	struct ng_pipe_run *run;
	struct ng_pipe_cfg *cfg;
	int error = 0;

	NGI_GET_MSG(item, msg);
	switch (msg->header.typecookie) {
	case NGM_PIPE_COOKIE:
		switch (msg->header.cmd) {
		case NGM_PIPE_GET_STATS:
		case NGM_PIPE_CLR_STATS:
		case NGM_PIPE_GETCLR_STATS:
			if (msg->header.cmd != NGM_PIPE_CLR_STATS) {
				NG_MKRESPONSE(resp, msg,
				    sizeof(*stats), M_NOWAIT);
				if (resp == NULL) {
					error = ENOMEM;
					break;
				}
				stats = (struct ng_pipe_stats *) resp->data;
				bcopy(&priv->upper.stats, &stats->downstream,
				    sizeof(stats->downstream));
				bcopy(&priv->lower.stats, &stats->upstream,
				    sizeof(stats->upstream));
			}
			if (msg->header.cmd != NGM_PIPE_GET_STATS) {
				bzero(&priv->upper.stats,
				    sizeof(priv->upper.stats));
				bzero(&priv->lower.stats,
				    sizeof(priv->lower.stats));
			}
			break;
		case NGM_PIPE_GET_RUN:
			NG_MKRESPONSE(resp, msg, sizeof(*run), M_NOWAIT);
			if (resp == NULL) {
				error = ENOMEM;
				break;
			}
			run = (struct ng_pipe_run *) resp->data;
			bcopy(&priv->upper.run, &run->downstream,
				sizeof(run->downstream));
			bcopy(&priv->lower.run, &run->upstream,
				sizeof(run->upstream));
			break;
		case NGM_PIPE_GET_CFG:
			NG_MKRESPONSE(resp, msg, sizeof(*cfg), M_NOWAIT);
			if (resp == NULL) {
				error = ENOMEM;
				break;
			}
			cfg = (struct ng_pipe_cfg *) resp->data;
			bcopy(&priv->upper.cfg, &cfg->downstream,
				sizeof(cfg->downstream));
			bcopy(&priv->lower.cfg, &cfg->upstream,
				sizeof(cfg->upstream));
			if (cfg->upstream.bandwidth ==
			    cfg->downstream.bandwidth) {
				cfg->bandwidth = cfg->upstream.bandwidth;
				cfg->upstream.bandwidth = 0;
				cfg->downstream.bandwidth = 0;
			} else
				cfg->bandwidth = 0;
			break;
		case NGM_PIPE_SET_CFG:
			cfg = (struct ng_pipe_cfg *) msg->data;
			if (msg->header.arglen != sizeof(*cfg)) {
				error = EINVAL;
				break;
			}

			if (cfg->bandwidth == -1) {
				priv->upper.cfg.bandwidth = 0;
				priv->lower.cfg.bandwidth = 0;
			} else if (cfg->bandwidth >= 100 &&
			    cfg->bandwidth <= 1000000000) {
				priv->upper.cfg.bandwidth = cfg->bandwidth;
				priv->lower.cfg.bandwidth = cfg->bandwidth;
			}

			parse_cfg(&priv->upper.cfg, &cfg->downstream,
			    &priv->upper, priv);
			parse_cfg(&priv->lower.cfg, &cfg->upstream,
			    &priv->lower, priv);

                        break;
		default:
			error = EINVAL;
			break;
		}
		break;
	default:
		error = EINVAL;
		break;
	}
	NG_RESPOND_MSG(error, node, item, resp);
	NG_FREE_MSG(msg);

	return (error);
}

static void
parse_cfg(struct ng_pipe_hookcfg *current, struct ng_pipe_hookcfg *new,
	struct hookinfo *hinfo, priv_p priv)
{

	if (new->qin_size_limit == -1)
		current->qin_size_limit = 0;
	else if (new->qin_size_limit >= 5)
		current->qin_size_limit = new->qin_size_limit;

	if (new->fifo) {
		current->fifo = 1;
		current->drr = 0;
	}

	if (new->drr) {
		current->fifo = 0;
		/* DRR quantum */
		if (new->drr >= 32)
			current->drr = new->drr;
		else
			current->drr = 2048;		/* default quantum */
	}

	if (new->bandwidth == -1) {
		current->bandwidth = 0;
		current->fifo = 1;
		current->drr = 0;
	} else if (new->bandwidth >= 100 && new->bandwidth <= 1000000000)
		current->bandwidth = new->bandwidth;

	if (current->bandwidth)
		hinfo->noqueue = 0;
	else
		hinfo->noqueue = 1;
}

/*
 * Compute a hash signature for a packet. Used system-wide hash functions
 * for IP v4 and v6. Here we expecting not-vlan-tagged Ethernet frames with IP
 * payload. For anything else it will return zero.
 */
static uint32_t
ip_hash(struct mbuf **m)
{
	struct ether_header *eh;
	struct ip      *ip4hdr;
	struct ip6_hdr *ip6hdr;


	 if ( (*m)->m_len < sizeof(struct ether_header) &&
	     (*m = m_pullup(*m, sizeof(struct ether_header))) == NULL) {
	 	return (0);
	 }

	eh = mtod(*m, struct ether_header *);

	/* Determine IP version and make corresponding hash.
	 * Fallback to zero if not successfull. */
	switch (ntohs(eh->ether_type)) {
	case ETHERTYPE_IP:
		if ( (*m)->m_len < sizeof(struct ether_header)+sizeof(struct ip) &&
		    (*m = m_pullup(*m, sizeof(struct ether_header)+sizeof(struct ip)))
		    == NULL)
			return (0);

		ip4hdr = mtodo(*m, ETHER_HDR_LEN);

		return ( INADDR_HASHVAL(ip4hdr->ip_src.s_addr)
			^INADDR_HASHVAL(ip4hdr->ip_dst.s_addr));
	break;
	case ETHERTYPE_IPV6:
		if ( (*m)->m_len < sizeof(struct ether_header)+sizeof(struct ip6_hdr) &&
		    (*m = m_pullup(*m, sizeof(struct ether_header)+sizeof(struct ip6_hdr)))
		    == NULL)
			return (0);

		ip6hdr = mtodo(*m, ETHER_HDR_LEN);

		return ( IN6ADDR_HASHVAL(&ip6hdr->ip6_src)
			^IN6ADDR_HASHVAL(&ip6hdr->ip6_dst));
	break;
	default:
	/* Not IPv4 or IPv6 */
		return 0;
	}

}

static inline void
hook_refill(struct hookinfo *hinfo, struct timeval *now)
{
	struct timeval timediff;
        u_int32_t cbs = hinfo->cfg.bandwidth/8;

	/*
	 * Refill token bucket. Once per tick, because I'm sure it will not refill
	 * again.
	 */
	timediff = *now;
	timevalsub(&timediff,&hinfo->last_refill);
	if (timevalisset(&timediff)) { /* At least one tick since last refill */
		if (timediff.tv_sec == 0) {
			hinfo->run.tc += (cbs*timediff.tv_usec/1000000 );
		/* We have hardcoded max tokens for one second on max bandwidth. */
			if (hinfo->run.tc > cbs) {
				hinfo->run.tc = cbs;
			}
		} else {
			hinfo->run.tc = cbs;
		}
		hinfo->last_refill = *now;
	}
}

static inline void
process_callout(struct hookinfo *hinfo, priv_p priv, node_p node)
{
	if (hinfo->run.qin_frames) {
		if (!priv->timer_scheduled) {
			ng_callout(&priv->timer, node, NULL, 1, ngpl_callout, NULL, 0);
			priv->timer_scheduled = 1;
		}
	} else if (!priv->upper.run.qin_frames
		 &&!priv->lower.run.qin_frames
		 &&priv->timer_scheduled) {
			ng_uncallout(&priv->timer, node);
			priv->timer_scheduled = 0;
	}
}

/*
 * Receive data on a hook - both in upstream and downstream direction.
 * We put the frame on the inbound queue, and try to initiate dequeuing
 * sequence immediately.
 */
int
ngpl_rcvdata(hook_p hook, item_p item)
{
	struct hookinfo * hinfo = NG_HOOK_PRIVATE(hook);
	const priv_p priv = NG_NODE_PRIVATE(NG_HOOK_NODE(hook));
	const node_p node = NG_HOOK_NODE(hinfo->hook);
	struct timeval uuptime;
	struct timeval *now = &uuptime;
	struct ngpl_fifo *ngpl_f = NULL;
	struct ngpl_hdr *ngpl_h = NULL;
	struct mbuf *m;
	uint32_t hash;
	u_int64_t psize;

	getmicrouptime(now);

	NGI_GET_M(item, m);
	KASSERT(m != NULL, ("NGI_GET_M failed"));

	psize = m->m_pkthdr.len;

	/* First, try to dequeue frames from queue(s) if any. Or at least refill tokens */
	if (hinfo->run.qin_frames) {
		pipe_dequeue(hinfo, now);
	} else {
		hook_refill(hinfo, now);
	}

	/* If queue is empty and there's enough tokens, just forward frame, don't enqueue it.
	 */
	if (((!hinfo->run.qin_frames) && hinfo->run.tc >= psize) || hinfo->noqueue) {
		int error = 0;
		struct hookinfo *dest;

		/* Which one is the destination hook? */
		dest = (hinfo == &priv->lower)?(&priv->upper):(&priv->lower);

		NG_FWD_NEW_DATA(error, item, dest->hook, m);

		if (!error) {
			hinfo->stats.fwd_frames++;
			hinfo->stats.fwd_octets += psize;
			/* Decrement tokens */
			hinfo->run.tc -= psize;
		}
		return(error);
	}

	if (hinfo->cfg.fifo)
		hash = 0;	/* all packets go into a single FIFO queue */
	else {
		hash = ip_hash(&m) ^ NGPL_QUEUES;
		if (m == NULL) /* ip_hash() couldnt pullup and freed mbuf */ {
			NG_FREE_ITEM(item);
			return (ENOBUFS);
		}
	}

	/* Populate the packet header */
	ngpl_h = uma_zalloc(ngpl_zone_hdr, M_NOWAIT);
	KASSERT((ngpl_h != NULL), ("ngpl_h zalloc failed (1)"));
	ngpl_h->m = m;
	ngpl_h->item = item;

	/* Find the appropriate FIFO queue for the packet and enqueue it*/
	ngpl_f = hinfo->fifo_array[hash];

	if (ngpl_f == NULL) {
		ngpl_f = uma_zalloc(ngpl_zone_fifo, M_NOWAIT);
		KASSERT(ngpl_h != NULL, ("ngpl_h zalloc failed (2)"));
		hinfo->fifo_array[hash] = ngpl_f;
		TAILQ_INIT(&ngpl_f->packet_head);
		ngpl_f->hash = hash;
		ngpl_f->packets = 1;
		ngpl_f->rr_deficit = hinfo->cfg.drr;	/* DRR quantum */
		hinfo->run.fifo_queues++;
		TAILQ_INSERT_TAIL(&ngpl_f->packet_head, ngpl_h, ngpl_link);
		TAILQ_INSERT_TAIL(&hinfo->fifo_head, ngpl_f, fifo_le);
	} else {
		/* Discard THIS frame if inbound queue limit is still reached. */
		if (ngpl_f->packets >= hinfo->cfg.qin_size_limit) {
			hinfo->stats.in_disc_octets += psize;
			hinfo->stats.in_disc_frames++;
			NG_FREE_ITEM(item);
			NG_FREE_M(m);
			return (0);
		}

		TAILQ_INSERT_TAIL(&ngpl_f->packet_head, ngpl_h, ngpl_link);
		ngpl_f->packets++;
	}
	hinfo->run.qin_frames++;
	hinfo->run.qin_octets += psize;

	process_callout(hinfo, priv, node);

	return (0);
}


/*
 * Dequeueing sequence - we basically do the following:
 * TODO: rewrite.
 */
void
pipe_dequeue(struct hookinfo *hinfo, struct timeval *now) {
	const node_p node = NG_HOOK_NODE(hinfo->hook);
	const priv_p priv = NG_NODE_PRIVATE(node);
	struct hookinfo *dest;
	struct ngpl_fifo *ngpl_f;
	struct ngpl_hdr *ngpl_h;
	item_p item;
	struct mbuf *m;
	int error = 0;
	u_int64_t psize;

	hook_refill(hinfo, now);

	/* Which one is the destination hook? */
	dest = (hinfo == &priv->lower)?(&priv->upper):(&priv->lower);

	/* Bandwidth queue processing */
	while ((ngpl_f = TAILQ_FIRST(&hinfo->fifo_head))) {
		ngpl_h = TAILQ_FIRST(&ngpl_f->packet_head);
		item = ngpl_h->item;
		m = ngpl_h->m;
		psize = m->m_pkthdr.len;

		/* Stop queue processing if there's not enougth tokens */
		if (psize > hinfo->run.tc)
			break;

		/* Deficit Round Robin (DRR) processing */
		if (hinfo->cfg.drr) {
			if (ngpl_f->rr_deficit >= psize) {
				ngpl_f->rr_deficit -= psize;
			} else {
				ngpl_f->rr_deficit += hinfo->cfg.drr;
				TAILQ_REMOVE(&hinfo->fifo_head, ngpl_f, fifo_le);
				TAILQ_INSERT_TAIL(&hinfo->fifo_head,
				    ngpl_f, fifo_le);
				continue;
			}
		}

		/* Actually dequeue packet */
		TAILQ_REMOVE(&ngpl_f->packet_head, ngpl_h, ngpl_link);
		uma_zfree(ngpl_zone_hdr, ngpl_h);
		hinfo->run.qin_frames--;
		hinfo->run.qin_octets -= psize;
		ngpl_f->packets--;

		if (!ngpl_f->packets) {
			TAILQ_REMOVE(&hinfo->fifo_head, ngpl_f, fifo_le);
			hinfo->fifo_array[ngpl_f->hash] = NULL;
			uma_zfree(ngpl_zone_fifo, ngpl_f);
			hinfo->run.fifo_queues--;
		}

		NG_FWD_NEW_DATA(error, item, dest->hook, m);

		if (!error) {
			hinfo->stats.fwd_frames++;
			hinfo->stats.fwd_octets += psize;
			/* Decrement tokens */
			hinfo->run.tc -= psize;
		}
	}

	process_callout(hinfo, priv, node);
}

/*
 * This routine is called on every clock tick.  We poll connected hooks
 * for queued frames by calling pipe_dequeue().
 */
static void
ngpl_callout(node_p node, hook_p hook, void *arg1, int arg2)
{
	const priv_p priv = NG_NODE_PRIVATE(node);
	struct timeval now;

	priv->timer_scheduled = 0;
	getmicrouptime(&now);
	if (priv->upper.hook != NULL)
		pipe_dequeue(&priv->upper, &now);
	if (priv->lower.hook != NULL)
		pipe_dequeue(&priv->lower, &now);
}

/*
 * Shutdown processing
 *
 * This is tricky. If we have both a lower and upper hook, then we
 * probably want to extricate ourselves and leave the two peers
 * still linked to each other. Otherwise we should just shut down as
 * a normal node would.
 */
static int
ngpl_shutdown(node_p node)
{
	const priv_p priv = NG_NODE_PRIVATE(node);

	if (priv->timer_scheduled)
		ng_uncallout(&priv->timer, node);
	if (priv->lower.hook && priv->upper.hook)
		ng_bypass(priv->lower.hook, priv->upper.hook);
	else {
		if (priv->upper.hook != NULL)
			ng_rmhook_self(priv->upper.hook);
		if (priv->lower.hook != NULL)
			ng_rmhook_self(priv->lower.hook);
	}
	NG_NODE_UNREF(node);
	free(priv, M_NG_PIPE_LT);
	return (0);
}


/*
 * Hook disconnection
 */
static int
ngpl_disconnect(hook_p hook)
{
	struct hookinfo *const hinfo = NG_HOOK_PRIVATE(hook);
	struct ngpl_fifo *ngpl_f;
	struct ngpl_hdr *ngpl_h;

	KASSERT(hinfo != NULL, ("%s: null info", __FUNCTION__));
	hinfo->hook = NULL;

	/* Flush all fifo queues associated with the hook */
	while ((ngpl_f = TAILQ_FIRST(&hinfo->fifo_head))) {
		while ((ngpl_h = TAILQ_FIRST(&ngpl_f->packet_head))) {
			TAILQ_REMOVE(&ngpl_f->packet_head, ngpl_h, ngpl_link);
			NG_FREE_ITEM(ngpl_h->item); /* it also frees mbuf */
			uma_zfree(ngpl_zone_hdr, ngpl_h);
		}
		TAILQ_REMOVE(&hinfo->fifo_head, ngpl_f, fifo_le);
		hinfo->fifo_array[ngpl_f->hash] = NULL;
		uma_zfree(ngpl_zone_fifo, ngpl_f);
	}

	/* Autoshutdown on last hook  disconnect */
	if ((NG_NODE_NUMHOOKS(NG_HOOK_NODE(hook)) == 0)
		&& (NG_NODE_IS_VALID(NG_HOOK_NODE(hook)))) /* already shutting down? */
			ng_rmnode_self(NG_HOOK_NODE(hook));

	return (0);
}

static int
ngpl_modevent(module_t mod, int type, void *unused)
{
	int error = 0;

	switch (type) {
	case MOD_LOAD:
		ngpl_zone_hdr = uma_zcreate("ng_pipe_lite_hdr", sizeof(struct ngpl_hdr),
			NULL, NULL, NULL, NULL, UMA_ALIGN_PTR, 0);
		if (ngpl_zone_hdr == NULL)
			panic("ng_pipe_lt: couldn't allocate descriptor zone for hdr's");
		ngpl_zone_fifo = uma_zcreate("ng_pipe_lite_fifo", sizeof (struct ngpl_fifo),
			NULL, NULL, NULL, NULL, UMA_ALIGN_PTR, 0);
		if (ngpl_zone_fifo == NULL)
			panic("ng_pipe_lt: couldn't allocate descriptor zone for FIFOs");
		break;
	case MOD_UNLOAD:
		uma_zdestroy(ngpl_zone_hdr);
		uma_zdestroy(ngpl_zone_fifo);
		break;
	default:
		error = EOPNOTSUPP;
		break;
	}

	return (error);
}

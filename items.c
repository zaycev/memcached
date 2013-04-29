/* -*- Mode: C; tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*- */
#include "memcached.h"
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/signal.h>
#include <sys/resource.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <errno.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <assert.h>

/* Forward Declarations */
static void item_link_q(item *it, const int instance_id);
static void item_unlink_q(item *it, const int instance_id);

/*
 * We only reposition items in the LRU queue if they haven't been repositioned
 * in this many seconds. That saves us from churning on frequently-accessed
 * items.
 */
#define ITEM_UPDATE_INTERVAL 60

#define LARGEST_ID POWER_LARGEST
typedef struct {
    uint64_t evicted;
    uint64_t evicted_nonzero;
    rel_time_t evicted_time;
    uint64_t reclaimed;
    uint64_t outofmemory;
    uint64_t tailrepairs;
    uint64_t expired_unfetched;
    uint64_t evicted_unfetched;
} itemstats_t;

static item ***heads;
static item ***tails;
static itemstats_t **itemstats;
static unsigned int **sizes;

void item_stats_reset(const int num_instances) {
    int i=0;
    mutex_lock(&cache_lock);
    //Temporary way to reset stats, should change to memset on individual itemstats
    for(i=0;i<num_instances;i++){
        free(itemstats[i]);
        itemstats[i] = calloc(LARGEST_ID,sizeof(itemstats_t));
    }
    mutex_unlock(&cache_lock);
}


/* Get the next CAS id for a new item. */
uint64_t get_cas_id(void) {
    static uint64_t cas_id = 0;
    return ++cas_id;
}

/* Enable this for reference-count debugging. */
#if 0
# define DEBUG_REFCNT(it,op) \
                fprintf(stderr, "item %x refcnt(%c) %d %c%c%c\n", \
                        it, op, it->refcount, \
                        (it->it_flags & ITEM_LINKED) ? 'L' : ' ', \
                        (it->it_flags & ITEM_SLABBED) ? 'S' : ' ')
#else
# define DEBUG_REFCNT(it,op) while(0)
#endif

/**
 * Generates the variable-sized part of the header for an object.
 *
 * key     - The key
 * nkey    - The length of the key
 * flags   - key flags
 * nbytes  - Number of bytes to hold value and addition CRLF terminator
 * suffix  - Buffer for the "VALUE" line suffix (flags, size).
 * nsuffix - The length of the suffix is stored here.
 *
 * Returns the total size of the header.
 */
static size_t item_make_header(const uint8_t nkey, const int flags, const int nbytes,
                     char *suffix, uint8_t *nsuffix) {
    /* suffix is defined at 40 chars elsewhere.. */
    *nsuffix = (uint8_t) snprintf(suffix, 40, " %d %d\r\n", flags, nbytes - 2);
    return sizeof(item) + nkey + *nsuffix + nbytes;
}

/*@null@*/
item *do_item_alloc(char *key, const size_t nkey, const int flags,
                    const rel_time_t exptime, const int nbytes,
                    const uint32_t cur_hv, const int instance_id) {
    uint8_t nsuffix;
    item *it = NULL;
    char suffix[40];
    size_t ntotal = item_make_header(nkey + 1, flags, nbytes, suffix, &nsuffix);
    if (settings.use_cas) {
        ntotal += sizeof(uint64_t);
    }

    unsigned int id = slabs_clsid(ntotal,instance_id);
    if (id == 0)
        return 0;

    do_instance_lock(instance_id);
    mutex_lock(&cache_lock);
    /* do a quick check if we have any expired items in the tail.. */
    int tries = 5;
    int tried_alloc = 0;
    item *search;
    void *hold_lock = NULL;
    rel_time_t oldest_live = settings.oldest_live;

    search = tails[instance_id][id];
    /* We walk up *only* for locked items. Never searching for expired.
     * Waste of CPU for almost all deployments */
    for (; tries > 0 && search != NULL; tries--, search=search->prev) {
        uint32_t hv = hash(ITEM_key(search), search->nkey, 0);
        /* Attempt to hash item lock the "search" item. If locked, no
         * other callers can incr the refcount
         */
        /* FIXME: I think we need to mask the hv here for comparison? */
        if (hv != cur_hv && (hold_lock = item_trylock(hv, instance_id)) == NULL)
            continue;
        /* Now see if the item is refcount locked */
        if (refcount_incr(&search->refcount) != 2) {
            refcount_decr(&search->refcount);
            /* Old rare bug could cause a refcount leak. We haven't seen
             * it in years, but we leave this code in to prevent failures
             * just in case */
            if (search->time + TAIL_REPAIR_TIME < current_time) {
                itemstats[instance_id][id].tailrepairs++;
                search->refcount = 1;
                do_item_unlink_nolock(search, hv, instance_id);
            }
            if (hold_lock)
                item_trylock_unlock(hold_lock, instance_id);
            continue;
        }

        /* Expired or flushed */
        if ((search->exptime != 0 && search->exptime < current_time)
            || (search->time <= oldest_live && oldest_live <= current_time)) {
            itemstats[instance_id][id].reclaimed++;
            if ((search->it_flags & ITEM_FETCHED) == 0) {
                itemstats[instance_id][id].expired_unfetched++;
            }
            it = search;
            slabs_adjust_mem_requested(it->slabs_clsid, ITEM_ntotal(it), ntotal, instance_id);
            do_item_unlink_nolock(it, hv, instance_id);
            /* Initialize the item block: */
            it->slabs_clsid = 0;
        } else if ((it = slabs_alloc(ntotal, id, instance_id)) == NULL) {
            tried_alloc = 1;
            if (settings.evict_to_free == 0) {
                itemstats[instance_id][id].outofmemory++;
            } else {
                itemstats[instance_id][id].evicted++;
                itemstats[instance_id][id].evicted_time = current_time - search->time;
                if (search->exptime != 0)
                    itemstats[instance_id][id].evicted_nonzero++;
                if ((search->it_flags & ITEM_FETCHED) == 0) {
                    itemstats[instance_id][id].evicted_unfetched++;
                }
                it = search;
                slabs_adjust_mem_requested(it->slabs_clsid, ITEM_ntotal(it), ntotal, instance_id);
                do_item_unlink_nolock(it, hv, instance_id);
                /* Initialize the item block: */
                it->slabs_clsid = 0;

                /* If we've just evicted an item, and the automover is set to
                 * angry bird mode, attempt to rip memory into this slab class.
                 * TODO: Move valid object detection into a function, and on a
                 * "successful" memory pull, look behind and see if the next alloc
                 * would be an eviction. Then kick off the slab mover before the
                 * eviction happens.
                 */
                if (settings.slab_automove == 2)
                    slabs_reassign(-1, id);
            }
        }

        refcount_decr(&search->refcount);
        /* If hash values were equal, we don't grab a second lock */
        if (hold_lock)
            item_trylock_unlock(hold_lock, instance_id);
        break;
    }

    if (!tried_alloc && (tries == 0 || search == NULL))
        it = slabs_alloc(ntotal, id, instance_id);

    if (it == NULL) {
        itemstats[instance_id][id].outofmemory++;
        mutex_unlock(&cache_lock);
        return NULL;
    }

    assert(it->slabs_clsid == 0);
    assert(it != heads[instance_id][id]);

    /* Item initialization can happen outside of the lock; the item's already
     * been removed from the slab LRU.
     */
    it->refcount = 1;     /* the caller will have a reference */
    mutex_unlock(&cache_lock);
    do_instance_unlock(instance_id);

    it->next = it->prev = it->h_next = 0;
    it->slabs_clsid = id;

    DEBUG_REFCNT(it, '*');
    it->it_flags = settings.use_cas ? ITEM_CAS : 0;
    it->nkey = nkey;
    it->nbytes = nbytes;
    memcpy(ITEM_key(it), key, nkey);
    it->exptime = exptime;
    memcpy(ITEM_suffix(it), suffix, (size_t)nsuffix);
    it->nsuffix = nsuffix;
    return it;
}

void item_free(item *it) {
    size_t ntotal = ITEM_ntotal(it);
    unsigned int clsid;
    int instance_id = get_instance_id(ITEM_key(it), it->nkey, 0, settings.num_instances);
    assert((it->it_flags & ITEM_LINKED) == 0);
    assert(it != heads[instance_id][it->slabs_clsid]);
    assert(it != tails[instance_id][it->slabs_clsid]);
    assert(it->refcount == 0);

    /* so slab size changer can tell later if item is already free or not */
    clsid = it->slabs_clsid;
    it->slabs_clsid = 0;
    DEBUG_REFCNT(it, 'F');
    slabs_free(it, ntotal, clsid, instance_id);
}

/**
 * Returns true if an item will fit in the cache (its size does not exceed
 * the maximum for a cache entry.)
 */
bool item_size_ok(const size_t nkey, const int flags, const int nbytes, const int instance_id) {
    char prefix[40];
    uint8_t nsuffix;

    size_t ntotal = item_make_header(nkey + 1, flags, nbytes,
                                     prefix, &nsuffix);
    if (settings.use_cas) {
        ntotal += sizeof(uint64_t);
    }

    return slabs_clsid(ntotal,instance_id) != 0;
}

static void item_link_q(item *it, const int instance_id) { /* item is the new head */
    item **head, **tail;
    assert(it->slabs_clsid < LARGEST_ID);
    assert((it->it_flags & ITEM_SLABBED) == 0);

    head = &heads[instance_id][it->slabs_clsid];
    tail = &tails[instance_id][it->slabs_clsid];
    assert(it != *head);
    assert((*head && *tail) || (*head == 0 && *tail == 0));
    it->prev = 0;
    it->next = *head;
    if (it->next) it->next->prev = it;
    *head = it;
    if (*tail == 0) *tail = it;
    sizes[instance_id][it->slabs_clsid]++;
    return;
}

static void item_unlink_q(item *it, const int instance_id) {
    item **head, **tail;
    assert(it->slabs_clsid < LARGEST_ID);
    head = &heads[instance_id][it->slabs_clsid];
    tail = &tails[instance_id][it->slabs_clsid];

    if (*head == it) {
        assert(it->prev == 0);
        *head = it->next;
    }
    if (*tail == it) {
        assert(it->next == 0);
        *tail = it->prev;
    }
    assert(it->next != it);
    assert(it->prev != it);

    if (it->next) it->next->prev = it->prev;
    if (it->prev) it->prev->next = it->next;
    sizes[instance_id][it->slabs_clsid]--;
    return;
}

int do_item_link(item *it, const uint32_t hv, const int instance_id) {
    MEMCACHED_ITEM_LINK(ITEM_key(it), it->nkey, it->nbytes);
    assert((it->it_flags & (ITEM_LINKED|ITEM_SLABBED)) == 0);
    mutex_lock(&cache_lock);
    it->it_flags |= ITEM_LINKED;
    it->time = current_time;

    STATS_LOCK();
    stats.curr_bytes += ITEM_ntotal(it);
    stats.curr_items += 1;
    stats.total_items += 1;
    STATS_UNLOCK();

    /* Allocate a new CAS ID on link. */
    ITEM_set_cas(it, (settings.use_cas) ? get_cas_id() : 0);
    assoc_insert(it, hv, instance_id);
    item_link_q(it, instance_id);
    refcount_incr(&it->refcount);
    mutex_unlock(&cache_lock);

    return 1;
}

void do_item_unlink(item *it, const uint32_t hv, const int instance_id) {
    MEMCACHED_ITEM_UNLINK(ITEM_key(it), it->nkey, it->nbytes);
    mutex_lock(&cache_lock);
    if ((it->it_flags & ITEM_LINKED) != 0) {
        it->it_flags &= ~ITEM_LINKED;
        STATS_LOCK();
        stats.curr_bytes -= ITEM_ntotal(it);
        stats.curr_items -= 1;
        STATS_UNLOCK();
        assoc_delete(ITEM_key(it), it->nkey, hv, instance_id);
        item_unlink_q(it, instance_id);
        do_item_remove(it);
    }
    mutex_unlock(&cache_lock);
}

/* FIXME: Is it necessary to keep this copy/pasted code? */
void do_item_unlink_nolock(item *it, const uint32_t hv, const int instance_id) {
    MEMCACHED_ITEM_UNLINK(ITEM_key(it), it->nkey, it->nbytes);
    if ((it->it_flags & ITEM_LINKED) != 0) {
        it->it_flags &= ~ITEM_LINKED;
        STATS_LOCK();
        stats.curr_bytes -= ITEM_ntotal(it);
        stats.curr_items -= 1;
        STATS_UNLOCK();
        assoc_delete(ITEM_key(it), it->nkey, hv, instance_id);
        item_unlink_q(it, instance_id);
        do_item_remove(it);
    }
}

void do_item_remove(item *it) {
    MEMCACHED_ITEM_REMOVE(ITEM_key(it), it->nkey, it->nbytes);
    assert((it->it_flags & ITEM_SLABBED) == 0);

    if (refcount_decr(&it->refcount) == 0) {
        item_free(it);
    }
}

void do_item_update(item *it) {
    int instance_id=get_instance_id(ITEM_key(it), it->nkey, 0,  settings.num_instances);
    MEMCACHED_ITEM_UPDATE(ITEM_key(it), it->nkey, it->nbytes);
    if (it->time < current_time - ITEM_UPDATE_INTERVAL) {
        assert((it->it_flags & ITEM_SLABBED) == 0);

        mutex_lock(&cache_lock);
        if ((it->it_flags & ITEM_LINKED) != 0) {
            item_unlink_q(it, instance_id);
            it->time = current_time;
            item_link_q(it, instance_id);
        }
        mutex_unlock(&cache_lock);
    }
}

int do_item_replace(item *it, item *new_it, const uint32_t hv, const int instance_id) {
    MEMCACHED_ITEM_REPLACE(ITEM_key(it), it->nkey, it->nbytes,
                           ITEM_key(new_it), new_it->nkey, new_it->nbytes);
    assert((it->it_flags & ITEM_SLABBED) == 0);

    do_item_unlink(it, hv, instance_id);
    return do_item_link(new_it, hv, instance_id);
}

/*@null@*/
char *do_item_cachedump(const unsigned int slabs_clsid, const unsigned int limit, unsigned int *bytes) {
    unsigned int memlimit = 2 * 1024 * 1024;   /* 2MB max response size */
    char *buffer;
    unsigned int bufcurr;
    item *it;
    unsigned int len;
    unsigned int shown = 0;
    char key_temp[KEY_MAX_LENGTH + 1];
    char temp[512];
    int i=0;


    buffer = malloc((size_t)memlimit);
    if (buffer == 0) return NULL;
    bufcurr = 0;

    for(i=0; i < settings.num_instances; i++){
        it = heads[i][slabs_clsid];
        while (it != NULL && (limit == 0 || shown < limit)) {
            assert(it->nkey <= KEY_MAX_LENGTH);
            /* Copy the key since it may not be null-terminated in the struct */
            strncpy(key_temp, ITEM_key(it), it->nkey);
            key_temp[it->nkey] = 0x00; /* terminate */
            len = snprintf(temp, sizeof(temp), "ITEM %s [%d b; %lu s]\r\n",
                           key_temp, it->nbytes - 2,
                           (unsigned long)it->exptime + process_started);
            if (bufcurr + len + 6 > memlimit)  /* 6 is END\r\n\0 */
                break;
            memcpy(buffer + bufcurr, temp, len);
            bufcurr += len;
            shown++;
            it = it->next;
        }
    }

    memcpy(buffer + bufcurr, "END\r\n", 6);
    bufcurr += 5;

    *bytes = bufcurr;
    return buffer;
}

void item_stats_evictions(uint64_t *evicted) {
    int i,instance_id;
    mutex_lock(&cache_lock);
    for (instance_id = 0; instance_id < settings.num_instances; instance_id++) {
        for (i = 0; i < LARGEST_ID; i++) {
            evicted[i] = itemstats[instance_id][i].evicted;
        }
    }
    mutex_unlock(&cache_lock);
}

void do_item_stats_totals(ADD_STAT add_stats, void *c) {
    itemstats_t totals;
    memset(&totals, 0, sizeof(itemstats_t));
    int i,instance_id;
    for (instance_id = 0; instance_id < settings.num_instances; instance_id++) {
        for (i = 0; i < LARGEST_ID; i++) {
            totals.expired_unfetched += itemstats[instance_id][i].expired_unfetched;
            totals.evicted_unfetched += itemstats[instance_id][i].evicted_unfetched;
            totals.evicted += itemstats[instance_id][i].evicted;
            totals.reclaimed += itemstats[instance_id][i].reclaimed;
        }
    }
    APPEND_STAT("expired_unfetched", "%llu",
                (unsigned long long)totals.expired_unfetched);
    APPEND_STAT("evicted_unfetched", "%llu",
                (unsigned long long)totals.evicted_unfetched);
    APPEND_STAT("evictions", "%llu",
                (unsigned long long)totals.evicted);
    APPEND_STAT("reclaimed", "%llu",
                (unsigned long long)totals.reclaimed);
}

void do_item_stats(ADD_STAT add_stats, void *c) {
    int i,instance_id;
    for (instance_id = 0; instance_id < settings.num_instances; instance_id++) {
        for (i = 0; i < LARGEST_ID; i++) {
            if (tails[instance_id][i] != NULL) {
                const char *fmt = "items:%d:%s";
                char key_str[STAT_KEY_LEN];
                char val_str[STAT_VAL_LEN];
                int klen = 0, vlen = 0;
                if (tails[instance_id][i] == NULL) {
                    /* We removed all of the items in this slab class */
                    continue;
                }
                APPEND_NUM_FMT_STAT(fmt, i, "number", "%u", sizes[instance_id][i]);
                APPEND_NUM_FMT_STAT(fmt, i, "age", "%u", current_time - tails[instance_id][i]->time);
                APPEND_NUM_FMT_STAT(fmt, i, "evicted",
                                    "%llu", (unsigned long long)itemstats[instance_id][i].evicted);
                APPEND_NUM_FMT_STAT(fmt, i, "evicted_nonzero",
                                    "%llu", (unsigned long long)itemstats[instance_id][i].evicted_nonzero);
                APPEND_NUM_FMT_STAT(fmt, i, "evicted_time",
                                    "%u", itemstats[instance_id][i].evicted_time);
                APPEND_NUM_FMT_STAT(fmt, i, "outofmemory",
                                    "%llu", (unsigned long long)itemstats[instance_id][i].outofmemory);
                APPEND_NUM_FMT_STAT(fmt, i, "tailrepairs",
                                    "%llu", (unsigned long long)itemstats[instance_id][i].tailrepairs);
                APPEND_NUM_FMT_STAT(fmt, i, "reclaimed",
                                    "%llu", (unsigned long long)itemstats[instance_id][i].reclaimed);
                APPEND_NUM_FMT_STAT(fmt, i, "expired_unfetched",
                                    "%llu", (unsigned long long)itemstats[instance_id][i].expired_unfetched);
                APPEND_NUM_FMT_STAT(fmt, i, "evicted_unfetched",
                                    "%llu", (unsigned long long)itemstats[instance_id][i].evicted_unfetched);
            }
        }
    }

    /* getting here means both ascii and binary terminators fit */
    add_stats(NULL, 0, NULL, 0, c);
}

/** dumps out a list of objects of each size, with granularity of 32 bytes */
/*@null@*/
void do_item_stats_sizes(ADD_STAT add_stats, void *c) {

    /* max 1MB object, divided into 32 bytes size buckets */
    const int num_buckets = 32768;
    unsigned int *histogram = calloc(num_buckets, sizeof(int));

    if (histogram != NULL) {
        int i, instance_id;
        for (instance_id = 0; instance_id < settings.num_instances; instance_id++) {
            /* build the histogram */
            for (i = 0; i < LARGEST_ID; i++) {
                item *iter = heads[instance_id][i];
                while (iter) {
                    int ntotal = ITEM_ntotal(iter);
                    int bucket = ntotal / 32;
                    if ((ntotal % 32) != 0) bucket++;
                    if (bucket < num_buckets) histogram[bucket]++;
                    iter = iter->next;
                }
            }
        }
        /* write the buffer */
        for (i = 0; i < num_buckets; i++) {
            if (histogram[i] != 0) {
                char key[8];
                snprintf(key, sizeof(key), "%d", i * 32);
                APPEND_STAT(key, "%u", histogram[i]);
            }
        }
        free(histogram);
    }
    add_stats(NULL, 0, NULL, 0, c);
}

/** wrapper around assoc_find which does the lazy expiration logic */
item *do_item_get(const char *key, const size_t nkey, const uint32_t hv, const int instance_id) {
    //mutex_lock(&cache_lock);
    item *it = assoc_find(key, nkey, hv, instance_id);
    if (it != NULL) {
        refcount_incr(&it->refcount);
        /* Optimization for slab reassignment. prevents popular items from
         * jamming in busy wait. Can only do this here to satisfy lock order
         * of item_lock, cache_lock, slabs_lock. */
        if (slab_rebalance_signal &&
            ((void *)it >= slab_rebal.slab_start && (void *)it < slab_rebal.slab_end)) {
            do_item_unlink_nolock(it, hv, instance_id);
            do_item_remove(it);
            it = NULL;
        }
    }
    //mutex_unlock(&cache_lock);
    int was_found = 0;

    if (settings.verbose > 2) {
        if (it == NULL) {
            fprintf(stderr, "> NOT FOUND %s", key);
        } else {
            fprintf(stderr, "> FOUND KEY %s", ITEM_key(it));
            was_found++;
        }
    }

    if (it != NULL) {
        if (settings.oldest_live != 0 && settings.oldest_live <= current_time &&
            it->time <= settings.oldest_live) {
            do_item_unlink(it, hv, instance_id);
            do_item_remove(it);
            it = NULL;
            if (was_found) {
                fprintf(stderr, " -nuked by flush");
            }
        } else if (it->exptime != 0 && it->exptime <= current_time) {
            do_item_unlink(it, hv, instance_id);
            do_item_remove(it);
            it = NULL;
            if (was_found) {
                fprintf(stderr, " -nuked by expire");
            }
        } else {
            it->it_flags |= ITEM_FETCHED;
            DEBUG_REFCNT(it, '+');
        }
    }

    if (settings.verbose > 2)
        fprintf(stderr, "\n");

    return it;
}

item *do_item_touch(const char *key, size_t nkey, uint32_t exptime,
                    const uint32_t hv, const int instance_id) {
    item *it = do_item_get(key, nkey, hv, instance_id);
    if (it != NULL) {
        it->exptime = exptime;
    }
    return it;
}

/* expires items that are more recent than the oldest_live setting. */
void do_item_flush_expired(void) {
    int i, instance_id;
    item *iter, *next;
    if (settings.oldest_live == 0)
        return;
    for (instance_id = 0; instance_id < settings.num_instances; instance_id++) {
        for (i = 0; i < LARGEST_ID; i++) {
            /* The LRU is sorted in decreasing time order, and an item's timestamp
             * is never newer than its last access time, so we only need to walk
             * back until we hit an item older than the oldest_live time.
             * The oldest_live checking will auto-expire the remaining items.
             */
            for (iter = heads[instance_id][i]; iter != NULL; iter = next) {
                if (iter->time >= settings.oldest_live) {
                    next = iter->next;
                    if ((iter->it_flags & ITEM_SLABBED) == 0) {
                        do_item_unlink_nolock(iter, hash(ITEM_key(iter), iter->nkey, 0), instance_id);
                    }
                } else {
                    /* We've hit the first old item. Continue to the next queue. */
                    break;
                }
            }
        }
    }
}

void lru_init(const int num_instances){
    int i=0;
    heads = calloc(num_instances, sizeof(item **));
    tails = calloc(num_instances, sizeof(item **));
    itemstats = calloc(num_instances, sizeof(itemstats_t *));
    sizes = calloc(num_instances, sizeof(unsigned int *));

    for(i=0;i<num_instances;i++){
        heads[i] = calloc(LARGEST_ID, sizeof(item *));
        tails[i] = calloc(LARGEST_ID, sizeof(item *));
        itemstats[i] = calloc(LARGEST_ID,sizeof(itemstats_t));
        sizes[i] = calloc(LARGEST_ID,sizeof(unsigned int));

        if (! heads[i] || !tails[i] || !itemstats[i] || !sizes[i]) {
            fprintf(stderr, "Failed to init LRU.\n");
            exit(EXIT_FAILURE);
        }
    }
}

/* -*- Mode: C; tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*- */
/*
 * Hash table
 *
 * The hash function used here is by Bob Jenkins, 1996:
 *    <http://burtleburtle.net/bob/hash/doobs.html>
 *       "By Bob Jenkins, 1996.  bob_jenkins@burtleburtle.net.
 *       You may use this code any way you wish, private, educational,
 *       or commercial.  It's free."
 *
 * The rest of the file is licensed under the BSD license.  See LICENSE.
 */

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
#include <assert.h>
#include <pthread.h>

typedef  unsigned long  int  ub4;   /* unsigned 4-byte quantities */
typedef  unsigned       char ub1;   /* unsigned 1-byte quantities */

/* how many powers of 2's worth of buckets we use */
unsigned int hashpower = HASHPOWER_DEFAULT;

#define hashsize(n) ((ub4)1<<(n))
#define hashmask(n) (hashsize(n)-1)

/* Main hash table. This is where we look except during expansion. */
static item*** primary_hashtable = 0;

/*
 * Previous hash table. During expansion, we look here for keys that haven't
 * been moved over to the primary yet.
 */
static item*** old_hashtable = 0;

/* Number of items in the hash table. */
static unsigned int hash_items = 0;

/* Flag: Are we in the middle of expanding now? */
static bool *expanding = 0;
static bool *started_expanding = 0;

/*
 * During expansion we migrate values with bucket granularity; this is how
 * far we've gotten so far. Ranges from 0 .. hashsize(hashpower - 1) - 1.
 */
static unsigned int expand_bucket = 0;

void assoc_init(const int hashtable_init,const int num_instances) {
    int i=0;
    if (hashtable_init) {
        hashpower = hashtable_init;
    }
    expanding = calloc(num_instances, sizeof(bool*));
    started_expanding = calloc(num_instances, sizeof(bool*));
    for(i=0;i<num_instances;i++){
    expanding[i]=false;
    started_expanding[i]=false;

    }

    primary_hashtable = calloc(num_instances, sizeof(void **));
    for(i=0;i<num_instances;i++){
        primary_hashtable[i] = calloc(hashsize(hashpower), sizeof(void *));
        if (! primary_hashtable[i]) {
            fprintf(stderr, "Failed to init hashtable.\n");
            exit(EXIT_FAILURE);
        }
    }
    STATS_LOCK();
    stats.hash_power_level = hashpower;
    stats.hash_bytes = hashsize(hashpower) * sizeof(void *);
    STATS_UNLOCK();
}

item *assoc_find(const char *key, const size_t nkey, const uint32_t hv, const int instance_id) {
    item *it;
    unsigned int oldbucket;

    if (expanding[instance_id] &&
        (oldbucket = (hv & hashmask(hashpower - 1))) >= expand_bucket)
    {
        it = old_hashtable[instance_id][oldbucket];
    } else {
        it = primary_hashtable[instance_id][hv & hashmask(hashpower)];
    }

    item *ret = NULL;
    int depth = 0;
    while (it) {
        if ((nkey == it->nkey) && (memcmp(key, ITEM_key(it), nkey) == 0)) {
            ret = it;
            break;
        }
        it = it->h_next;
        ++depth;
    }
    MEMCACHED_ASSOC_FIND(key, nkey, depth);
    return ret;
}

/* returns the address of the item pointer before the key.  if *item == 0,
   the item wasn't found */

static item** _hashitem_before (const char *key, const size_t nkey, const uint32_t hv, const int instance_id) {
    item **pos;
    unsigned int oldbucket;

    if (expanding[instance_id] &&
        (oldbucket = (hv & hashmask(hashpower - 1))) >= expand_bucket)
    {
        pos = &old_hashtable[instance_id][oldbucket];
    } else {
        pos = &primary_hashtable[instance_id][hv & hashmask(hashpower)];
    }

    while (*pos && ((nkey != (*pos)->nkey) || memcmp(key, ITEM_key(*pos), nkey))) {
        pos = &(*pos)->h_next;
    }
    return pos;
}

/* grows the hashtable to the next power of 2. */
static void assoc_expand(const int instance_id) {
    old_hashtable[instance_id] = primary_hashtable[instance_id];

    primary_hashtable[instance_id] = calloc(hashsize(hashpower + 1), sizeof(void *));
    if (primary_hashtable[instance_id]) {
        if (settings.verbose > 1)
            fprintf(stderr, "Hash table expansion starting\n");
        hashpower++;
        expanding[instance_id] = true;
        expand_bucket = 0;
        STATS_LOCK();
        stats.hash_power_level = hashpower;
        stats.hash_bytes += hashsize(hashpower) * sizeof(void *);
        stats.hash_is_expanding = 1;
        STATS_UNLOCK();
    } else {
        primary_hashtable[instance_id] = old_hashtable[instance_id];
        /* Bad news, but we can keep running. */
    }
}

static volatile int do_run_maintenance_thread = 1;

#define DEFAULT_HASH_BULK_MOVE 1
int hash_bulk_move = DEFAULT_HASH_BULK_MOVE;

static void expand_table_inline(int instance_id){
       int ii = 0;

        /* Lock the cache, and bulk move multiple buckets to the new
         * hash table. */
        item_lock_global(instance_id);
        mutex_lock(&cache_lock);

        for (ii = 0; ii < hash_bulk_move && expanding[instance_id]; ++ii) {
            item *it, *next;
            int bucket;

            for (it = old_hashtable[instance_id][expand_bucket]; NULL != it; it = next) {
                next = it->h_next;

                bucket = hash(ITEM_key(it), it->nkey, 0) & hashmask(hashpower);
                it->h_next = primary_hashtable[instance_id][bucket];
                primary_hashtable[instance_id][bucket] = it;
            }

            old_hashtable[expand_bucket] = NULL;

            expand_bucket++;
            if (expand_bucket == hashsize(hashpower - 1)) {
                expanding[instance_id] = false;
                free(old_hashtable[instance_id]);
                STATS_LOCK();
                stats.hash_bytes -= hashsize(hashpower - 1) * sizeof(void *);
                stats.hash_is_expanding = 0;
                STATS_UNLOCK();
                if (settings.verbose > 1)
                    fprintf(stderr, "Hash table expansion done\n");
            }
        }

        mutex_unlock(&cache_lock);
        item_unlock_global(instance_id);

        if (!expanding[instance_id]) {
            /* finished expanding. tell all threads to use fine-grained locks */
            switch_item_lock_type(ITEM_LOCK_GRANULAR);
            slabs_rebalancer_resume();
            /* We are done expanding.. just wait for next invocation */
            mutex_lock(&cache_lock);
            started_expanding[instance_id] = false;
            /* Before doing anything, tell threads to use a global lock */
            mutex_unlock(&cache_lock);
            slabs_rebalancer_pause();
            switch_item_lock_type(ITEM_LOCK_GLOBAL);
            mutex_lock(&cache_lock);
            assoc_expand(instance_id);
            mutex_unlock(&cache_lock);
        }
}

/* Note: this isn't an assoc_update.  The key must not already exist to call this */
int assoc_insert(item *it, const uint32_t hv, const int instance_id) {
    unsigned int oldbucket;

//    assert(assoc_find(ITEM_key(it), it->nkey) == 0);  /* shouldn't have duplicately named things defined */

    if (expanding[instance_id] &&
        (oldbucket = (hv & hashmask(hashpower - 1))) >= expand_bucket)
    {
        it->h_next = old_hashtable[instance_id][oldbucket];
        old_hashtable[instance_id][oldbucket] = it;
    } else {
        it->h_next = primary_hashtable[instance_id][hv & hashmask(hashpower)];
        primary_hashtable[instance_id][hv & hashmask(hashpower)] = it;
    }

    hash_items++;
    if (! expanding[instance_id] && hash_items > (hashsize(hashpower) * 3) / 2) {
        expand_table_inline(instance_id);
    }

    MEMCACHED_ASSOC_INSERT(ITEM_key(it), it->nkey, hash_items);
    return 1;
}

void assoc_delete(const char *key, const size_t nkey, const uint32_t hv, const int instance_id) {
    item **before = _hashitem_before(key, nkey, hv, instance_id);

    if (*before) {
        item *nxt;
        hash_items--;
        /* The DTrace probe cannot be triggered as the last instruction
         * due to possible tail-optimization by the compiler
         */
        MEMCACHED_ASSOC_DELETE(key, nkey, hash_items);
        nxt = (*before)->h_next;
        (*before)->h_next = 0;   /* probably pointless, but whatever. */
        *before = nxt;
        return;
    }
    /* Note:  we never actually get here.  the callers don't delete things
       they can't find. */
    assert(*before != 0);
}

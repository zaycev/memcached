#ifndef HASH_H
#define    HASH_H

#ifdef    __cplusplus
extern "C" {
#endif

uint32_t hash(const void *key, size_t length, const uint32_t initval);
uint32_t get_instance_id(const void *key, size_t length, const uint32_t initval, const uint32_t num_instances);

#ifdef    __cplusplus
}
#endif

#endif    /* HASH_H */


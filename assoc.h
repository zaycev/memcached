/* associative array */
void assoc_init(const int hashpower_init,const int num_instances);
item *assoc_find(const char *key, const size_t nkey, const uint32_t hv, const int instance_id);
int assoc_insert(item *item, const uint32_t hv, const int instance_id);
void assoc_delete(const char *key, const size_t nkey, const uint32_t hv, const int instance_id);
void do_assoc_move_next_bucket(void);
extern unsigned int hashpower;

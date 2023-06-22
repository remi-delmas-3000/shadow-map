#ifndef CPROVER_SHADOW_MAP_DEFINED
#define CPROVER_SHADOW_MAP_DEFINED
#include <stdlib.h>

/*
  A shadow map allows to map any individual byte of an object manipulated
  by user code to 2^k shadow bytes.

  A shadow map is modelled as a finite map from object IDs to lazily allocated
  shadow objects. The size of a shadow object is 2^k times the size of its
  source object. The map size is set to 2^nof-object-bits to accomodate as many
  objects as possible in any symex run.

  Given a pointer `ptr` to some user byte, a pointer to the start of the k
  shadow bytes is obtained by changing the base address of `ptr` and scaling
  its offset by 2^k by right-shifting k bits.

  It is possible to allocate several different shadow maps with different k
  values in a same program.
*/

typedef struct {
  // shift value
  size_t shift;
  // array of pointers to shadow objects
  void **ptrs;
} shadow_map_t;

extern size_t __CPROVER_max_malloc_size;
int __builtin_clzll(unsigned long long);

// computes 2^OBJECT_BITS
#define __nof_objects                                                          \
  ((size_t)(1ULL << __builtin_clzll(__CPROVER_max_malloc_size)))

// Initialises the given shadow memory map
void shadow_map_init(shadow_map_t *smap, size_t shadow_bytes_per_byte) {
  __CPROVER_assert(1 == shadow_bytes_per_byte || 2 == shadow_bytes_per_byte ||
                       4 == shadow_bytes_per_byte || 8 == shadow_bytes_per_byte,
                   "shadow_bytes_per_byte must be in {1, 2, 4, 8}");
  size_t shift = 3;
  if (shadow_bytes_per_byte == 1) {
    shift = 0;
  } else if (shadow_bytes_per_byte == 2) {
    shift = 1;
  } else if (shadow_bytes_per_byte <= 4) {
    shift = 2;
  }
  __CPROVER_assert(shift <= 3, "8 shadow bytes per byte at most");
  *smap = (shadow_map_t){
      .shift = shift,
      .ptrs = __CPROVER_allocate(__nof_objects * sizeof(void *), 1)};
}

// Returns a pointer to the shadow bytes of the byte pointed to by ptr
void *shadow_map_get(shadow_map_t *smap, void *ptr) {
  __CPROVER_size_t id = __CPROVER_POINTER_OBJECT(ptr);
  __CPROVER_size_t size = __CPROVER_OBJECT_SIZE(ptr);
  __CPROVER_size_t offset = __CPROVER_POINTER_OFFSET(ptr);

  size_t max_size = SIZE_MAX >> smap->shift;
  __CPROVER_assert(size <= max_size, " no overflow on size shift");
  __CPROVER_assert(offset <= max_size, " no overflow on offset shift");

  // fetch pointer to the shadow object
  void *sptr = smap->ptrs[id];
  if (!sptr) {
    // create shadow object if NULL
    sptr = __CPROVER_allocate(size << smap->shift, 1);
    smap->ptrs[id] = sptr;
  }
  // rebase pointer and scale offset
  return sptr + (offset << smap->shift);
}

#endif

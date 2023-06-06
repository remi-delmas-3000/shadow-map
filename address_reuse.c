#include "shadow_map.h"
#include <stdbool.h>
#include <stdlib.h>

typedef struct shadow_alloc_s {
  bool live;
  size_t size;
  size_t base_address;
} shadow_alloc_t;

shadow_map_t mem_map;

void mem_map_init() {
  // 8 bytes per byte, enough to store a pointer to a shadow_alloc_t struct
  shadow_map_init(&mem_map, 3);
}

// gets the shadow allocation object
shadow_alloc_t *get_shadow_mem(void *alloc) {
  __CPROVER_assert(__CPROVER_DYNAMIC_OBJECT(alloc) &&
                       __CPROVER_POINTER_OFFSET(alloc) == 0,
                   "dyn alloc");
  shadow_alloc_t **shadow_ptr_ptr =
      (shadow_alloc_t **)shadow_map_get(&mem_map, alloc);
  if (*shadow_ptr_ptr == NULL) {
    shadow_alloc_t *res = __CPROVER_allocate(sizeof(shadow_alloc_t), 1);
    *shadow_ptr_ptr = res;
    return res;
  }
  return *shadow_ptr_ptr;
  return NULL;
}

// set the live bit to false
void __alloc_free(void *free_ptr) {
  shadow_alloc_t *shadow = get_shadow_mem(free_ptr);
  shadow->live = false;
}

// initialize a shadow alloc object
void __alloc_init(void *alloc_ptr, size_t size) {

  size_t base_address;
  // ensure whole object is addressable
  __CPROVER_assume(base_address < SIZE_MAX - size);

  // do not reuse any live address
  for (size_t i = 0; i < __nof_objects; i++) {
    shadow_alloc_t **shadow_ptr_ptr = (shadow_alloc_t **)mem_map.ptrs[i];
    if (shadow_ptr_ptr != NULL) {
      if (*shadow_ptr_ptr != NULL) {
        shadow_alloc_t *sh = (shadow_alloc_t *)*shadow_ptr_ptr;
        if (sh->live) {
          size_t ba = sh->base_address;
          __CPROVER_assume((base_address < ba) ||
                           (base_address > ba + sh->size));
        }
      }
    }
  }
  shadow_alloc_t *shadow = get_shadow_mem(alloc_ptr);
  shadow->live = true;
  shadow->base_address = base_address;
  shadow->size = size;
}

// lifts pointer comparison to base addresses
bool __same_base_address(void *x, void *y) {
  __CPROVER_assert(
      __CPROVER_DYNAMIC_OBJECT(x) && __CPROVER_POINTER_OFFSET(x) == 0, "dyn x");
  __CPROVER_assert(
      __CPROVER_DYNAMIC_OBJECT(y) && __CPROVER_POINTER_OFFSET(y) == 0, "dyn y");
  return (get_shadow_mem(x)->base_address == get_shadow_mem(y)->base_address);
}

#if 0
void main() {
    int *x = malloc(sizeof(int));
    int *y = malloc(sizeof(int));
    free(x);
    int *z = malloc(sizeof(int));
    if(x == y) {
       __CPROVER_assert(false, "x == y");
    }
    if(x == z) {
       __CPROVER_assert(false, "x == z");
    }
}
#endif

void main() {
  mem_map_init();
  int *x = malloc(sizeof(int));
  __alloc_init(x, sizeof(int));
  int *y = malloc(sizeof(int));
  __alloc_init(y, sizeof(int));
  free(x);
  __alloc_free(x);
  int *z = malloc(sizeof(int));
  __CPROVER_assert(__CPROVER_same_object(x, y), "same_object(x, y)");
  __CPROVER_assert(!__same_base_address(x, y), "!__same_base_address(x, y)");
  if (x == y) {
    __CPROVER_assert(false, "x == y");
  }
  __CPROVER_assert(__CPROVER_same_object(x, y), "same_object(x, z)");
  __CPROVER_assert(!__same_base_address(x, z), "!__same_base_address(x, z)");
  if (x == z) {
    __CPROVER_assert(false, "x == z");
  }
}

// [main.assertion.1] line 102 same_object(x, y): FAILURE
// [main.assertion.2] line 103 !__same_base_address(x, y): SUCCESS
// [main.assertion.3] line 105 x == y: SUCCESS
// [main.assertion.4] line 107 same_object(x, z): FAILURE
// [main.assertion.5] line 108 !__same_base_address(x, z): FAILURE
// [main.assertion.6] line 110 x == z: SUCCESS

#include "shadow_map.h"
#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

typedef struct my_struct_s {
  bool a;
  bool b;
} my_struct_t;

// set up shadow state to track number of writes
typedef struct my_shadow_struct_s {
  size_t nof_true_writes_a;
  size_t nof_false_writes_a;
  size_t nof_true_writes_b;
  size_t nof_false_writes_b;
} my_shadow_struct_t;

shadow_map_t shadow_struct_map;

void shadow_struct_map_init() {
  // 8 bytes per byte, enough to store a pointer to a shadow struct
  shadow_map_init(&shadow_struct_map, 3);
}

my_shadow_struct_t *get_shadow_struct(my_struct_t *ptr) {
  my_shadow_struct_t **shadow_ptr_ptr =
      (my_shadow_struct_t **)shadow_map_get(&shadow_struct_map, ptr);
  if (*shadow_ptr_ptr == NULL) {
    my_shadow_struct_t *res = __CPROVER_allocate(sizeof(my_shadow_struct_t), 1);
    *shadow_ptr_ptr = res;
    return res;
  }
  return *shadow_ptr_ptr;
}

int main() {

  shadow_struct_map_init();

  my_struct_t array[10];
  __CPROVER_array_set(array, 0);

  size_t i;
  if (i < 10) {
    my_shadow_struct_t *shadow = get_shadow_struct(&array[i]);
    bool nda = nondet_bool();
    if (nda) {
      shadow->nof_true_writes_a += 1;
    } else {
      shadow->nof_false_writes_a += 1;
    }
    array[i].a = nda;
    bool ndb = nondet_bool();
    if (ndb) {
      shadow->nof_true_writes_b += 1;
    } else {
      shadow->nof_false_writes_b += 1;
    }
    array[i].b = ndb;
  }

  if (i < 10) {
    my_shadow_struct_t *shadow = get_shadow_struct(&array[i]);
    assert(shadow->nof_false_writes_a + shadow->nof_true_writes_a == 1);
    assert(shadow->nof_false_writes_b + shadow->nof_true_writes_b == 1);
  } else {
    my_shadow_struct_t *shadow = get_shadow_struct(&array[0]);
    assert(shadow->nof_false_writes_a + shadow->nof_true_writes_a == 0);
    assert(shadow->nof_false_writes_b + shadow->nof_true_writes_b == 0);
  }
}

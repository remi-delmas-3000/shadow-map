#include <stdbool.h>
#include <stdlib.h>

/* This shows how to model address reuse by malloc using shadow memory.

The idea is to
- keep using CBMC's default (object_id, offset) encoding of pointer values,
- use the object_id as a unique generational index for an allocation,
- use that object_id as a key into a shadow map that tracks the object lifetime,
  size, and nondeterministic base address.

Every time an new object is allocated, we give it a non-deterministic base address that
is constrained to be within the bounds of the address space,
small enough free space after it to hold the object without overflowing the address space,
and outside of any of the currently alive object's address ranges.

This shadow information allows us to compute a full-width pointer
value from a CBMC pointer value by adding the nondeterministic base address and the offset.

We can then evaluate pointer equality or pointer relations on the full width
pointer value instead of the original (id, offset), and capture the consequences
of address reuse.

*/

/* This struct holds the shadow state we use to keep track the lifetime and size of individual objects. */
typedef struct shadow_alloc_s
{
  // is the object alive ?
  bool live;
  // the size of the object
  size_t size;
  // the base address of the object
  size_t base_address;
} shadow_alloc_t;

// shadow map that encodes a mapping from `objet_ids` to `shadow_alloc_t`
shadow_alloc_t *alloc_map;

extern size_t __CPROVER_max_malloc_size;
int __builtin_clzll(unsigned long long);

// computes pow(2, OBJECT_BITS)
#define MAX_NOF_OBJECTS \
  ((size_t)(1ULL << __builtin_clzll(__CPROVER_max_malloc_size)))

// utility function: allocate shadow map
void __shadow_init()
{
  alloc_map = malloc(sizeof(shadow_alloc_t) * MAX_NOF_OBJECTS);
  __CPROVER_array_set(alloc_map, (shadow_alloc_t){.live = false, .size = 0, .base_address = 0});
}

// utility function: set the live bit to false for the object `__CROVER_POINTER_OBJECT(ptr)`
void __shadow_free(void *ptr)
{
  alloc_map[__CPROVER_POINTER_OBJECT(ptr)].live = false;
}

// utility function: initialize a shadow alloc object for `__CPROVER_POINTER_OBJECT(ptr)` and the given `size`.
void __shadow_malloc(void *ptr, size_t size)
{
  // a nondeterministic base address (understand as "there exists some base addres",
  // i.e. models that the memory allocator can do anything)
  size_t base_address;
  // ensure whole object is addressable
  __CPROVER_assume(base_address < SIZE_MAX - size);

  // do not reuse any live address
  // in the current form this is costly to unwind, but symex could handle this
  // as a primitive operation "generate a base address address that is not currently in use"
  for (size_t i = 0; i < MAX_NOF_OBJECTS; i++)
  {
    shadow_alloc_t shadow = alloc_map[i];
    if (shadow.live)
    {
      size_t ba = shadow.base_address;
      __CPROVER_assume((base_address < ba) || (base_address > ba + shadow.size));
    }
  }
  shadow_alloc_t new_shadow_alloc = (shadow_alloc_t){.live = true, .size = size, .base_address = base_address};
  alloc_map[__CPROVER_POINTER_OBJECT(ptr)] = new_shadow_alloc;
}

// utility function: lift pointer equality check to full-width pointer values
bool __pointer_eq(void *x, void *y)
{
  // our example only works with dynamic objects for now
  __CPROVER_precondition(__CPROVER_DYNAMIC_OBJECT(x), "pointer_eq: dyn x");
  __CPROVER_precondition(__CPROVER_DYNAMIC_OBJECT(y), "pointer_eq: dyn y");
  // compute full-width pointer values
  size_t x_full = alloc_map[__CPROVER_POINTER_OBJECT(x)].base_address + __CPROVER_POINTER_OFFSET(x);
  size_t y_full = alloc_map[__CPROVER_POINTER_OBJECT(y)].base_address + __CPROVER_POINTER_OFFSET(y);
  // return the result of the full-width pointer comparison
  return x_full == y_full;
}

#ifndef FULL_WIDTH
// run with `make address_reuse`
void main() {
    int *x = malloc(sizeof(int));
    int *y = malloc(sizeof(int));
    // holds as expected
    __CPROVER_assert(x != y, "expected to hold because x and y are both live");
    free(x);
    int *z = malloc(sizeof(int));
    // holds but shouldn't 
    __CPROVER_assert(x != z, "expected to fail because x was deallocated and z could reuse x's address");
}
#else
// run with `make address_reuse_full_width`
void main()
{
  __shadow_init();
  int *x = malloc(sizeof(int));
  __shadow_malloc(x, sizeof(int));
  int *y = malloc(sizeof(int));
  __shadow_malloc(y, sizeof(int));
  // holds as expected
  __CPROVER_assert(!__pointer_eq(x, y), "expected to hold because x and y are both live");
  free(x);
  __shadow_free(x);
  int *z = malloc(sizeof(int));
  // falsified as expected
  __CPROVER_assert(!__pointer_eq(x, z), "expected to fail because x was deallocated and z could reuse x's address");
}
#endif

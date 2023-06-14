#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

/**
 * This instrumentation pass illustrates how to encode assumptions about the
 * contents of havoced arrays using shadow memory and bulk array
 * operations, without using loops to initialise arrays with valid nondet
 * values.
 *
 * The shadow memory maintains one boolean per byte which tracks if a memory
 * location is tagged as being havoced.
 *
 * The assumption is supplied as a pair of predicate and generator function.
 *
 * The read and write functions for the user-defined array type are
 * instrumented to lookup the shadow bit and emit an assumption when
 * first reading a havoced value read.
 *
 * The instrumentation pass also eliminates loops by:
 * - turning nondet initialisation loops into bulk array operations
 * - using invariants to rewrite user loops into base + step encoding.
 *
 * We obtain a loop-free model that can be verified without unwinding.
 *
 * Remark: Havocing pointers cannot be deferred to the first read of the
 * pointer, because this would allow fresh objects created after between the
 * havoc and the read to be added to the points to set of the pointer.
 */

#include "shadow_map.h"

int nondet_int();
size_t nondet_size_t();

shadow_map_t __havoced;

void __init_havoced() {
  // 1 bytes per byte
  shadow_map_init(&__havoced, 0);
}

typedef struct S {
  bool even;
  int value;
};

// An S is valid iff `even` is 0 or 1 and set whenever `value` is even
bool S_is_valid(struct S s) {
  return (((s.even == 1) | (s.even == 0)) & ((s.value % 2 == 0) == s.even));
}

// Generates a valid valud using a unconstrained value and an assumption
// (the 3 padding bytes between even and value are unconstrained)
struct S S_nondet_valid() {
  struct S result = (struct S){.even = nondet_bool(), .value = nondet_int()};
  __CPROVER_assume(S_is_valid(result));
  return result;
}

// An array `arr` of struct S and its size `size`
typedef struct V {
  struct S *arr;
  size_t size;
};

// Reads
struct S V_index_read(struct V *vec, size_t i) {
  assert(vec && i < vec->size);
#ifdef UNBOUNDED
  bool *shadow = (bool *)shadow_map_get(&__havoced, &(vec->arr[i]));
  if (*shadow) {
    // in havoced state, emit assumption
    __CPROVER_assume(S_is_valid(vec->arr[i]));
  }
  *shadow = false;
#endif
  return vec->arr[i];
}

// Writes `s` at index `i` in `vec`.
void V_index_write(struct V *vec, size_t i, struct S s) {
  assert(vec && i < vec->size);
#ifdef UNBOUNDED
  // not in havoced state anymore
  *((bool *)shadow_map_get(&__havoced, &(vec->arr[i]))) = false;
#endif
  vec->arr[i] = s;
}

bool V_havoc_contents(struct V *vec) {
  assert(vec);
  assert(__CPROVER_rw_ok(vec->arr, vec->size * sizeof(struct S)));
#ifndef UNBOUNDED
  // Initialisation loop, write valid nondet values
  for (size_t i = 0; i < vec->size; i++) {
    V_index_write(vec, i, S_nondet_valid());
  }
#else
  // Transform initialisation loop into a loop-free bulk operations
  __CPROVER_havoc_object(vec->arr);
  __CPROVER_array_set((bool *)shadow_map_get(&__havoced, vec->arr), true);
#endif
}

// Initialises a struct V by allocating for the given size and writing
// valid nondet values. Returns true on initialisation success.
bool V_init(struct V *vec, size_t size) {
  assert(vec);
  *vec = (struct V){.arr = malloc(sizeof(struct S) * size), .size = size};

  if (!vec->arr)
    return false;

  V_havoc_contents(vec);

  return true;
}

// Checks that every value in vec is valid
bool V_is_valid(struct V *vec) {
  if (!vec)
    return false;

  size_t i = 0;

#ifndef UNBOUNDED
  while (i < vec->size)
    // clang-format off
  __CPROVER_assigns(i)
  __CPROVER_loop_invariant(i <= vec->size)
  __CPROVER_decreases(vec->size - i)
    // clang-format on
    {
      struct S s = V_index_read(vec, i);
      if (!S_is_valid(s))
        return false;
      i++;
    }
#else
  // transform loop into base + havoc + step
  __CPROVER_assert(i <= vec->size, "loop invariant base case");
  i = nondet_size_t();
  __CPROVER_assume(i <= vec->size);
  size_t decreases_old = vec->size - i;
  if (i < vec->size) {
    struct S s = V_index_read(vec, i);
    if (!S_is_valid(s))
      return false;
    i++;
    __CPROVER_assert(i <= vec->size, "loop invariant step case");
    __CPROVER_assert(decreases_old > vec->size - i, "loop variant step case");
    __CPROVER_assume(false);
  }
#endif
  return true;
}
int main() {
  __init_havoced();
  struct V vec;
#ifdef UNBOUNDED
  size_t size;
  __CPROVER_assume(0 < size && size < (SIZE_MAX) / sizeof(struct S));
#else
  // fix a particular size in the bounded case
  size_t size = SIZE;
#endif

  if (!V_init(&vec, size))
    return 1;

#ifdef BUG
  // write an unconstrained value at some nondet index, should make the
  // next assertion fail
  size_t j = nondet_size_t();
  if (j < size) {
    V_index_write(&vec, j,
                  (struct S){.even = nondet_bool(), .value = nondet_int()});
  }
#endif

  assert(V_is_valid(&vec));

  return 0;
}

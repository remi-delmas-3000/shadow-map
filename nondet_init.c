#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

/**
 * This instrumentation pass illustrates how to encode assumptions about the
 * contents of arbitrary sized nondet vectors using shadow memory and bulk array
 * operations, without using loops to initialise arrays with valid nondet
 * values.
 *
 * The shadow memory maintains one boolean per byte which tracks if a memory
 * location is tagged as being in a nondet but valid state.
 *
 * The assumption is supplied as a pair of a predicate and generator function.
 *
 * The read and write functions for the user-defined vector type are
 * instrumented to lookup the shadow bit and invoke the generator function when
 * first reading a havoced value read.
 *
 * The instrumentation pass also eliminates loops in user code:
 * The nondet-initialisation loop is replaced by a bulk array operations on the
 * shadow bits
 * The loop in user code is removed using the supplied invariant to generate a
 * base + step encoding.
 *
 * We obtain a loop-free model that can be verified without unwinding.
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

bool S_is_valid(struct S s) { return (s.value % 2 == 0) == s.even; }

struct S S_nondet_valid() {
  struct S result = (struct S){.even = nondet_bool(), .value = nondet_int()};
  __CPROVER_assume(S_is_valid(result));
  return result;
}

typedef struct V {
  struct S *arr;
  size_t size;
};

// return true on success
bool V_init(struct V *vec, size_t size) {
  assert(vec);
  *vec = (struct V){.arr = malloc(sizeof(struct S) * size), .size = size};

  if (!vec->arr)
    return false;

#ifdef UNBOUNDED
  // transform initialisation loop below into a loop-free bulk array operation
  __CPROVER_array_set((bool *)shadow_map_get(&__havoced, vec->arr), true);
#else
  for (size_t i = 0; i < size; i++) {
    vec->arr[i] = S_nondet_valid();
  }
#endif
  return true;
}

struct S V_index_read(struct V *vec, size_t i) {
  assert(vec && i < vec->size);
#ifdef UNBOUNDED
  bool *shadow = (bool *)shadow_map_get(&__havoced, &(vec->arr[i]));
  if (*shadow) {
    *shadow = false;
    vec->arr[i] = S_nondet_valid();
  }
#endif
  return vec->arr[i];
}

void V_index_write(struct V *vec, size_t i, struct S s) {
  assert(vec && i < vec->size);
#ifdef UNBOUNDED
  *((bool *)(&__havoced, &(vec->arr[i]))) = false;
#endif
  vec->arr[i] = s;
}

bool foo(struct V *vec) {
  if (!vec)
    return false;

  size_t i = 0;

#ifdef UNBOUNDED
  // transform loop into base + havoc + step
  __CPROVER_assert(i <= vec->size, "loop invariant base case");
  i = nondet_size_t();
  __CPROVER_assume(i <= vec->size);
  size_t decreases_old = vec->size - i;
  if (i < vec->size) {
    struct S s = V_index_read(vec, i);
    if ((s.value % 2 == 0) != s.even)
      return false;
    i++;
    __CPROVER_assert(i <= vec->size, "loop invariant step case");
    __CPROVER_assert(decreases_old > vec->size - i, "loop variant step case");
    __CPROVER_assume(false);
  }
#else
  while (i < vec->size)
    // clang-format off
  __CPROVER_assigns(i)
  __CPROVER_loop_invariant(i <= vec->size)
  __CPROVER_decreases(vec->size - i)
    // clang-format on
    {
      struct S s = V_index_read(vec, i);
      if ((s.value % 2 == 0) != s.even)
        return false;
      i++;
    }
#endif
  return true;
}
int main() {
  __init_havoced();
  struct V vec;
#ifdef UNBOUNDED
  size_t size;
  __CPROVER_assume(size < (SIZE_MAX) / sizeof(struct S));
#else
  // fix a particular size in the bounded case
  size_t size = SIZE;
#endif

  if (!V_init(&vec, size))
    return 1;

  assert(foo(&vec));

  return 0;
}

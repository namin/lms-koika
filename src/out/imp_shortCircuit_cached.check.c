/*****************************************
Emitting C Generated Code
*******************************************/
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
/*********** Datastructures ***********/
struct CachedStateT {
  int* vars;
  int* mem;
  int timer;
  int* cache_keys;
  int* cache_vals;
};
/**************** Snippet ****************/
struct CachedStateT Snippet(struct CachedStateT x0) {
  x0.timer = x0.timer + 1;
  x0.vars[0] = 1;
  x0.timer = x0.timer + 1;
  x0.vars[1] = 1;
  x0.timer = x0.timer + 1;
  while (({
    x0.timer = x0.timer + 1;
    x0.timer = x0.timer + 1;
    x0.vars[0] == 1 && ({
      x0.timer = x0.timer + 1;
      x0.vars[1] <= 5;
    });
  })) {
    x0.timer = x0.timer + 1;
    x0.timer = x0.timer + 1;
    x0.timer = x0.timer + 1;
    int x1 = x0.vars[1];
    int x2 = x0.cache_keys[0] == x1 ? ({
      x0.timer = x0.timer + 1;
      x0.cache_vals[0];
    }) : (x0.cache_keys[1] == x1 ? ({
      int x3 = x0.cache_vals[1];
      x0.cache_keys[1] = x0.cache_keys[0];
      x0.cache_vals[1] = x0.cache_vals[0];
      x0.cache_keys[0] = x1;
      x0.cache_keys[0] = x3;
      x0.timer = x0.timer + 1;
      x3;
    }) : ({
      int x4 = x0.mem[x1];
      x0.mem[x0.cache_keys[1]] = x0.cache_vals[1];
      x0.cache_keys[1] = x0.cache_keys[0];
      x0.cache_vals[1] = x0.cache_vals[0];
      x0.cache_keys[0] = x1;
      x0.cache_keys[0] = x4;
      x0.timer = x0.timer + 100;
      x4;
    }));
    x0.timer = x0.timer + 1;
    int x5 = x0.vars[1] + 20;
    int x6 = x0.cache_keys[0] == x5 ? ({
      x0.timer = x0.timer + 1;
      x0.cache_vals[0];
    }) : (x0.cache_keys[1] == x5 ? ({
      int x7 = x0.cache_vals[1];
      x0.cache_keys[1] = x0.cache_keys[0];
      x0.cache_vals[1] = x0.cache_vals[0];
      x0.cache_keys[0] = x5;
      x0.cache_keys[0] = x7;
      x0.timer = x0.timer + 1;
      x7;
    }) : ({
      int x8 = x0.mem[x5];
      x0.mem[x0.cache_keys[1]] = x0.cache_vals[1];
      x0.cache_keys[1] = x0.cache_keys[0];
      x0.cache_vals[1] = x0.cache_vals[0];
      x0.cache_keys[0] = x5;
      x0.cache_keys[0] = x8;
      x0.timer = x0.timer + 100;
      x8;
    }));
    if (!(x2 == x6)) {
      x0.timer = x0.timer + 1;
      x0.vars[0] = 0;
    }
    x0.timer = x0.timer + 1;
    x0.timer = x0.timer + 1;
    x0.vars[1] = x0.vars[1] + 1;
  }
  return x0;
}
/*****************************************
End of C Generated Code
*******************************************/
#define MEM_SIZE 30
#define SECRET_SIZE 5
#define SECRET_OFFSET 20
#define CACHE_SIZE 2
int bounded(int low, int high) {
  int x = nondet_uint();
  if (x < low) {
    x = low;
  }
  if (x > high) {
    x = high;
  }
  return x;
}
void init(struct CachedStateT *st) {
  st->timer = 0;
  st->mem = calloc(sizeof(int), MEM_SIZE);
  st->vars = calloc(sizeof(int), 2);
  st->cache_keys = calloc(sizeof(int), CACHE_SIZE);
}
int main(int argc, char* argv[]) {
  struct CachedStateT s1;
  init(&s1);
  struct CachedStateT s2;
  init(&s2);
  int i;
  int x;
  // initialize input
  // TODO (cwong): this is ugly
  for (i=0; i<SECRET_SIZE; i++) {
    x = bounded(0, 20);
    s1.mem[i] = x;
    s2.mem[i] = x;
  }
  // initialize cache
  for (i=0; i<CACHE_SIZE; i++) {
    x = bounded(0, MEM_SIZE);
    s1.cache_keys[i] = x;
    s2.cache_keys[i] = x;
    s1.cache_vals[i] = s1.mem[x];
    s2.cache_vals[i] = s2.mem[x];
  }
  // initialize secret
  for (i=0; i<SECRET_SIZE; i++) {
    s1.mem[i+SECRET_OFFSET] = bounded(0, 20);
    s2.mem[i+SECRET_OFFSET] = bounded(0, 20);
  }
  struct CachedStateT s1_ = Snippet(s1);
  struct CachedStateT s2_ = Snippet(s2);
  __CPROVER_assert(s1_.timer==s2_.timer, "timing leak");
  return 0;
}

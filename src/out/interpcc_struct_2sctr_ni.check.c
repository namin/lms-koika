/*****************************************
Emitting C Generated Code
*******************************************/
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
/*********** Datastructures ***********/
struct stateT {
  int* regs;
  int* saved_regs;
  int* mem;
  int cache_key;
  int cache_val;
  int timer;
};
/************* Function Declarations **************/
struct stateT x1(struct stateT);
/************* Functions **************/
struct stateT x1(struct stateT x2) {
  x2.timer = x2.timer + 1;
  x2.timer = x2.timer + 1;
  x2.saved_regs[1] = x2.regs[1];
  int x3 = x2.regs[0];
  int x4 = x2.cache_key == x3 ? x2.cache_val : ({
    int x5 = x2.mem[x3];
    x2.timer = x2.timer + 1;
    x2.timer = x2.timer + 1;
    x2.cache_key = x3;
    x2.cache_val = x5;
    x5;
  });
  x2.regs[1] = x4;
  x2.timer = x2.timer + 1;
  x2.saved_regs[2] = x2.regs[2];
  int x6 = 4 + x2.regs[1];
  int x7 = x2.cache_key == x6 ? x2.cache_val : ({
    int x8 = x2.mem[x6];
    x2.timer = x2.timer + 1;
    x2.timer = x2.timer + 1;
    x2.cache_key = x6;
    x2.cache_val = x8;
    x8;
  });
  x2.regs[2] = x7;
  x2.timer = x2.timer + 1;
  if (x2.regs[0] == 0) {
    x2.regs[1] = x2.saved_regs[1];
    x2.regs[2] = x2.saved_regs[2];
  }
  return x2;
}
/**************** Snippet ****************/
struct stateT Snippet(struct stateT x0) {
  return x1(x0);
}
/*****************************************
End of C Generated Code
*******************************************/
#define NUM_REGS 3
#define MEM_SIZE 30
#define SECRET_SIZE 20
#define SECRET_OFFSET 10
int init(struct stateT *s) {
  s->regs = calloc(sizeof(int), NUM_REGS);
  s->cache_key = -1;
  s->cache_val = 0;
  s->timer = 0;
  s->mem = calloc(sizeof(int), NUM_REGS);
  for (int i=0; i<MEM_SIZE; i++) {
    s->mem[i] = 0;
  }
  return 0;
}
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
int main(int argc, char* argv[]) {
  struct stateT s1;
  init(&s1);
  struct stateT s2;
  init(&s2);
  int x = bounded(0, 20);
  s1.regs[0] = x;
  s2.regs[0] = x;
  int i;
  for (i=0; i<SECRET_SIZE; i++) {
    s1.mem[i+SECRET_OFFSET] = bounded(0, 20);
    s2.mem[i+SECRET_OFFSET] = bounded(0, 20);
  }
  struct stateT s1_ = Snippet(s1);
  struct stateT s2_ = Snippet(s2);
  __CPROVER_assert(s1_.timer==s2_.timer, "timing leak");
  return 0;
}

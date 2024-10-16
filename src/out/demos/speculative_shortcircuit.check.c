/*****************************************
Emitting C Generated Code
*******************************************/
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
/*********** Datastructures ***********/
struct StateT {
  int* regs;
  int* mem;
  int* saved_regs;
  int* cache_keys;
  int* cache_vals;
  int timer;
};
/************* Function Declarations **************/
struct StateT x1(struct StateT);
struct StateT x3(struct StateT);
struct StateT x5(struct StateT);
struct StateT x7(struct StateT);
struct StateT x10(struct StateT);
/************* Functions **************/
struct StateT x1(struct StateT x2) {
  x2.timer = x2.timer + 1;
  x2.regs[0] = 1;
  return x2;
}
struct StateT x3(struct StateT x4) {
  x4.timer = x4.timer + 1;
  return x4;
}
struct StateT x5(struct StateT x6) {
  x6.timer = x6.timer + 1;
  x6.regs[0] = 0;
  return x3(x6);
}
struct StateT x7(struct StateT x8) {
  x8.timer = x8.timer + 1;
  return x9(x8);
}
struct StateT x10(struct StateT x11) {
  x11.timer = x11.timer + 1;
  x11.regs[4] = x11.regs[4] + 1;
  return x7(x11);
}
/**************** Snippet ****************/
struct StateT Snippet(struct StateT x0) {
  return x12;
}
/*****************************************
End of C Generated Code
*******************************************/
#define NUM_REGS 8
#define MEM_SIZE 30
#define SECRET_SIZE 10
#define SECRET_OFFSET 20
#ifndef CBMC
#define __CPROVER_assert(b,s) 0
#define nondet_uint() 0
#else
int nondet_uint();
#endif
int bounded(int low, int high) {
  int x = nondet_uint();
  __CPROVER_assume(low <= x && x <= high);
  return x;
}
#define CACHE_LRU_SIZE 2
void init(struct StateT *s) {
  s->regs = calloc(sizeof(int), NUM_REGS);
  s->saved_regs = calloc(sizeof(int), NUM_REGS);
  for (int i=0; i<NUM_REGS; i++) {
    s->regs[i] = 0;
    s->saved_regs[i] = 0;
  }
  s->timer = 0;
  s->mem = calloc(sizeof(int), MEM_SIZE);
  for (int i=0; i<MEM_SIZE; i++) {
    s->mem[i] = 0;
  }
  s->cache_keys = calloc(sizeof(int), CACHE_LRU_SIZE);
  s->cache_vals = calloc(sizeof(int), CACHE_LRU_SIZE);
  for (int i=0; i<CACHE_LRU_SIZE; i++) {
    s->cache_keys[i] = -1;
    s->cache_vals[i] = -1;
  }
}
int main(int argc, char* argv[]) {
  struct StateT s1, s2;
  init(&s1);
  init(&s2);
  for (int i=0; i<SECRET_SIZE; i++) {
    int x = bounded(0, 20);
    s1.mem[i] = x;
    s2.mem[i] = x;
  }
  // initialize secret
  for (int i=0; i<SECRET_SIZE; i++) {
    s1.mem[SECRET_OFFSET+i] = bounded(0, 20);
    s2.mem[SECRET_OFFSET+i] = bounded(0, 20);
  }
  struct StateT s1_ = Snippet(s1);
  struct StateT s2_ = Snippet(s2);
  __CPROVER_assert(s1_.timer==s2_.timer, "timing leak");
  return 0;
}

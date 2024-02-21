/*****************************************
Emitting C Generated Code
*******************************************/
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
/************* Function Declarations **************/
struct StateT x1(struct StateT);
struct StateT x3(struct StateT);
struct StateT x5(struct StateT);
struct StateT x7(struct StateT);
/*********** Datastructures ***********/
struct StateT {
  int* regs;
  int* mem;
  int timer;
};
/************* Functions **************/
struct StateT x1(struct StateT x2) {
  x2.timer = x2.timer + 1;
  x2.regs[0] = x2.regs[1];
  return x2;
}
struct StateT x3(struct StateT x4) {
  x4.timer = x4.timer + 1;
  x4.regs[1] = x4.regs[1] * x4.regs[0];
  x4.timer = x4.timer + 1;
  x4.regs[2] = -1;
  x4.timer = x4.timer + 1;
  x4.regs[0] = x4.regs[0] + x4.regs[2];
  return x5(x4);
}
struct StateT x5(struct StateT x6) {
  return x6.regs[0] == 0 ? x1(x6) : x3(x6);
}
struct StateT x7(struct StateT x8) {
  x8.timer = x8.timer + 1;
  x8.regs[1] = 1;
  return x5(x8);
}
/**************** Snippet ****************/
struct StateT Snippet(struct StateT x0) {
  return x7(x0);
}
/*****************************************
End of C Generated Code
*******************************************/
#ifndef CBMC
#define __CPROVER_assert(b,s) 0
#define nondet_uint() 0
#define __CPROVER_assume(b) 0
#else
unsigned int nondet_uint();
#endif
int bounded(int low, int high) {
  int x = nondet_uint();
  __CPROVER_assume(low <= x && x <= high);
  return x;
}
int fact(int i) {
  if (i == 0) { return 1; }
  return i * fact(i-1);
}
int main(int argc, char *argv[]) {
  if (argc != 2) {
    printf("usage: %s <arg>\n", argv[0]);
    return 0;
  }
  struct StateT state;
  state.regs = calloc(8, sizeof(int));
  state.mem = calloc(1, sizeof(int));
  state.timer = 0;
  int input = bounded(0, 5);
  state.regs[0] = input;
  for (int i = 1; i < 8; i += 1) {
    state.regs[i] = 0;
  }
  for (int i = 0; i < 1; i += 1) {
    state.mem[i] = 0;
  }
  state = Snippet(state);
  __CPROVER_assert(state.regs[0] == fact(input), "correct evaluation");
  return 0;
}

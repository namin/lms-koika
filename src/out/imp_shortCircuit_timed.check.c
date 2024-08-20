/*****************************************
Emitting C Generated Code
*******************************************/
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
/*********** Datastructures ***********/
struct TimedStateT {
  int* vars;
  int* mem;
  int timer;
};
/**************** Snippet ****************/
struct TimedStateT Snippet(struct TimedStateT x0) {
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
    int* x1 = x0.vars;
    int* x2 = x0.mem;
    x0.timer = x0.timer + 1;
    if (!(x2[x1[1]] == x0.mem[x0.vars[1] + 20])) {
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
void init(struct TimedStateT *st) {
  st->timer = 0;
  st->mem = calloc(sizeof(int), MEM_SIZE);
  st->vars = calloc(sizeof(int), 2);
}
int main(int argc, char* argv[]) {
  struct TimedStateT s1;
  init(&s1);
  struct TimedStateT s2;
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
  // initialize secret
  for (i=0; i<SECRET_SIZE; i++) {
    s1.mem[i+SECRET_OFFSET] = bounded(0, 20);
    s2.mem[i+SECRET_OFFSET] = bounded(0, 20);
  }
  struct TimedStateT s1_ = Snippet(s1);
  struct TimedStateT s2_ = Snippet(s2);
  __CPROVER_assert(s1_.timer==s2_.timer, "timing leak");
  return 0;
}

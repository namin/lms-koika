#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>

#define EXTRA_OFFSET 5
#define MEM_SIZE 30
#define SECRET_SIZE 20
#define SECRET_OFFSET 10

struct State {
  int r0;
  int r1;
  int r2;
  int save_r0;
  int save_r1;
  int save_r2;
  int cache_key;
  int cache_val;
  int time;
  int mem[MEM_SIZE];
};

void Snippet(struct State s) {
  s.time = s.time + 2;
  s.save_r1 = s.r1;
  int x3 = s.r0;
  s.r1 = s.cache_key == x3 ? s.cache_val : ({
    int x4 = s.mem[x3];
    s.time = s.time + 2;
    s.cache_key = x3; s.cache_val = x4; x4; });
  s.time = s.time + 1;
  s.save_r2 = s.r2;
  int x5 = EXTRA_OFFSET + s.r1;
  s.r2 = s.cache_key == x5 ? s.cache_val : ({
    int x6 = s.mem[x5];
    s.time = s.time + 2;
    s.cache_key = x5; s.cache_val = x6; x6; });
  s.time = s.time + 1;
  if (s.r0 == 0) {
    s.r1 = s.save_r1;
    s.r2 = s.save_r2;
  }
}

int init(struct State s) {
  s.r0 = 0;
  s.r1 = 0;
  s.r2 = 0;
  s.save_r0 = 0;
  s.save_r1 = 0;
  s.save_r2 = 0;
  s.cache_key = -1;
  s.cache_val = 0;
  s.time = 0;
  for (int i=0; i<MEM_SIZE; i++) {
    s.mem[i] = 0;
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
  struct State s1;
  init(s1);
  struct State s2;
  init(s2);
  int x = bounded(0, 20);
  s1.r0 = x;
  s2.r0 = x;
  int i;
  for (i=0; i<SECRET_SIZE; i++) {
    s1.mem[i+SECRET_OFFSET] = bounded(0, 20);
    s2.mem[i+SECRET_OFFSET] = bounded(0, 20);
  }
  Snippet(s1);
  Snippet(s2);
  __CPROVER_assert(s1.time==s2.time, "no timing leak");
  return 0;
}

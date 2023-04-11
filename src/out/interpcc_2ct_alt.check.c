/*****************************************
Emitting C Generated Code
*******************************************/
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
/************* Function Declarations **************/
void x1(int*);
void x6(int*);
/************* Functions **************/
void x1(int* x2) {
  int x3 = x2[6] + 1;
  x2[6] = x3;
  int x4 = 4 + x2[1] + 10;
  x2[2] = x2[4] == x4 ? x2[5] : ({
    int x5 = x2[x4];
    x2[6] = x3 + 1 + 1;
    x2[4] = x4;
    x2[5] = x5;
    x5;
  });
}
void x6(int* x7) {
  int x8 = x7[6] + 1;
  x7[6] = x8;
  int x9 = x7[0] + 10;
  x7[1] = x7[4] == x9 ? x7[5] : ({
    int x10 = x7[x9];
    x7[6] = x8 + 1 + 1;
    x7[4] = x9;
    x7[5] = x10;
    x10;
  });
  x1(x7);
}
/**************** Snippet ****************/
void Snippet(int* x0) {
  x6(x0);
}
/*****************************************
End of C Generated Code
*******************************************/
int init(int* s) {
  for (int i=0; i<100; i++) {
    s[i] = 0;
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
  int s1[100];
  init(s1);
  int s2[100];
  init(s2);
  int x = bounded(0, 20);
  s1[0] = x;
  int i = 10+bounded(0, 20);
  s1[i] = 1;
  s2[0] = x;
  Snippet(s1);
  Snippet(s2);
  __CPROVER_assert(s1[6]==s2[6], "timing leak");
  return 0;
}

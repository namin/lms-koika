/*****************************************
Emitting C Generated Code
*******************************************/
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
/************* Function Declarations **************/
void x1(int*);
/************* Functions **************/
void x1(int* x2) {
  x2[6] = x2[6] + 1 + 1;
  x2[8] = x2[1];
  int x3 = x2[0] + 10;
  x2[1] = x2[4] == x3 ? x2[5] : ({
    int x4 = x2[x3];
    x2[6] = x2[6] + 1 + 1;
    x2[4] = x3;
    x2[5] = x4;
    x4;
  });
  x2[6] = x2[6] + 1;
  x2[9] = x2[2];
  int x5 = 4 + x2[1] + 10;
  x2[2] = x2[4] == x5 ? x2[5] : ({
    int x6 = x2[x5];
    x2[6] = x2[6] + 1 + 1;
    x2[4] = x5;
    x2[5] = x6;
    x6;
  });
  x2[6] = x2[6] + 1;
  if (x2[0] == 0) {
    x2[1] = x2[8];
    x2[2] = x2[9];
  }
}
/**************** Snippet ****************/
void Snippet(int* x0) {
  x1(x0);
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
  s2[0] = x;
  int i;
  for (i=0; i<20; i++) {
    s1[i+10] = bounded(0, 20);
    s2[i+10] = bounded(0, 20);
  }
  Snippet(s1);
  Snippet(s2);
  __CPROVER_assert(s1[6]==s2[6], "timing leak");
  return 0;
}

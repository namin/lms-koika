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
  int x3 = x2[6] + 1 + 1;
  x2[6] = x3;
  int x4 = x2[0] + 10;
  x2[1] = x2[4] == x4 ? x2[5] : ({
    int x5 = x2[x4];
    x2[6] = x3 + 1 + 1;
    x2[4] = x4;
    x2[5] = x5;
    x5;
  });
  int x6 = x2[6] + 1;
  x2[6] = x6;
  int x7 = 4 + x2[1] + 10;
  x2[2] = x2[4] == x7 ? x2[5] : ({
    int x8 = x2[x7];
    x2[6] = x6 + 1 + 1;
    x2[4] = x7;
    x2[5] = x8;
    x8;
  });
  x2[6] = x2[6] + 1;
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
int main(int argc, char* argv[]) {
  int s1[100];
  init(s1);
  s1[0] = 5;
  s1[15] = 1;
  int s2[100];
  init(s2);
  s2[0] = 5;
  Snippet(s1);
  Snippet(s2);
  __CPROVER_assert(s1[6]==s2[6], "timing leak");
  return 0;
}

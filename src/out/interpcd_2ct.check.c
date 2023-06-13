/*****************************************
Emitting C Generated Code
*******************************************/
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
/**************** Snippet ****************/
void Snippet(int* x0) {
  int x1 = 0;
  while (0 <= x1 && x1 < 2) {
    if (0 == x1) {
      int x2 = x0[6] + 1;
      x0[6] = x2;
      int x3 = x0[0] + 10;
      x0[1] = x0[4] == x3 ? x0[5] : ({
        int x4 = x0[x3];
        x0[6] = x2 + 1 + 1;
        x0[4] = x3;
        x0[5] = x4;
        x4;
      });
      x1 = 1;
    }
    if (1 == x1) {
      int x5 = x0[6] + 1;
      x0[6] = x5;
      int x6 = 4 + x0[1] + 10;
      x0[2] = x0[4] == x6 ? x0[5] : ({
        int x7 = x0[x6];
        x0[6] = x5 + 1 + 1;
        x0[4] = x6;
        x0[5] = x7;
        x7;
      });
      x1 = 2;
    }
  }
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
  int s2[100];
  init(s2);
  s1[0] = 5;
  s1[15] = 1;
  s2[0] = 5;
  Snippet(s1);
  Snippet(s2);
  __CPROVER_assert(s1[6]==s2[6], "timing leak");
  return 0;
}

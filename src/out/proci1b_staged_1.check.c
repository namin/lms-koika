/*****************************************
Emitting C Generated Code
*******************************************/
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
/**************** Snippet ****************/
int Snippet(int* x0) {
  int x1 = 0;
  while (0 <= x1 && x1 < 5) {
    if (0 == x1) {
      x0[3] = x0[2] + x0[1];
      x1 = x1 + 1;
    }
    if (1 == x1) {
      x0[1] = x0[2] + x0[0];
      x1 = x1 + 1;
    }
    if (2 == x1) {
      x0[2] = x0[3] + x0[0];
      x1 = x1 + 1;
    }
    if (3 == x1) {
      x0[4] = x0[4] + x0[5];
      x1 = x1 + 1;
    }
    if (4 == x1) if (x0[4] != 0) x1 = x1 + -4;
    else x1 = x1 + 1;
  }
  return x0[2];
}
/*****************************************
End of C Generated Code
*******************************************/
int main(int argc, char *argv[]) {
  int regfile[6] = {0, 0, 1, 0, 15, -1};
  int r = Snippet(regfile);
  printf("%d\n", r);
  return 0;
}

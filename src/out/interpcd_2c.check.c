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
      int x2 = x0[0] + 10;
      x0[1] = x0[4] == x2 ? x0[5] : ({
        int x3 = x0[x2];
        x0[4] = x2;
        x0[5] = x3;
        x3;
      });
      x1 = 1;
    }
    if (1 == x1) {
      int x4 = 4 + x0[1] + 10;
      x0[2] = x0[4] == x4 ? x0[5] : ({
        int x5 = x0[x4];
        x0[4] = x4;
        x0[5] = x5;
        x5;
      });
      x1 = 2;
    }
  }
}
/*****************************************
End of C Generated Code
*******************************************/
int main(int argc, char *argv[]) {
  if (argc != 2) {
    printf("usage: %s <arg>\n", argv[0]);
    return 0;
  }
  return 0;
}

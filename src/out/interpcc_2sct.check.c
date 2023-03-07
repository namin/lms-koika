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
int main(int argc, char *argv[]) {
  if (argc != 2) {
    printf("usage: %s <arg>\n", argv[0]);
    return 0;
  }
  return 0;
}

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
  int x3 = x2[0] + 10;
  int x4 = x2[4] == x3 ? x2[5] : ({
    int x5 = x2[x3];
    x2[4] = x3;
    x2[5] = x5;
    x5;
  });
  x2[1] = x4;
  int x6 = 4 + x4 + 10;
  x2[2] = x2[4] == x6 ? x2[5] : ({
    int x7 = x2[x6];
    x2[4] = x6;
    x2[5] = x7;
    x7;
  });
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

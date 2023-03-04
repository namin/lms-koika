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
  int x3 = x2[x2[0] + 4];
  x2[1] = x3;
  x2[2] = x2[4 + x3 + 4];
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

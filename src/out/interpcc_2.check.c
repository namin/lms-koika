/*****************************************
Emitting C Generated Code
*******************************************/
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
/************* Function Declarations **************/
void x1(int*);
void x3(int*);
void x5(int*);
/************* Functions **************/
void x1(int* x2) {
  x2[2] = x2[4 + x2[1] + 4];
}
void x3(int* x4) {
  x4[1] = x4[x4[0] + 4];
  x1(x4);
}
void x5(int* x6) {
  if (x6[0] == 0) {} else x3(x6);
}
/**************** Snippet ****************/
void Snippet(int* x0) {
  x5(x0);
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

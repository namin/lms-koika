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
/************* Functions **************/
void x1(int* x2) {
  if (x2[0] == 0) x3(x2);
}
void x3(int* x4) {
  x4[0] = x4[0] + x4[0];
  x1(x4);
}
/**************** Snippet ****************/
void Snippet(int* x0) {
  x3(x0);
}
/*****************************************
End of C Generated Code
*******************************************/
int main(int argc, char *argv[]) {
  if (argc != 2) {
    printf("usage: %s <arg>\n", argv[0]);
    return 0;
  }
  Snippet();
  return 0;
}

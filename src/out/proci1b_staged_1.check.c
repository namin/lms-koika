/*****************************************
Emitting C Generated Code
*******************************************/
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
/**************** Snippet ****************/
int* Snippet(int* x0) {
  int x1 = 0;
  int x2 = 0;
  int x3 = 0;
  while (0 <= x1 && x1 < 9) {
    if (0 == x1) {
      x0[x2] = x3;
      x2 = 2;
      x3 = x0[0] + 1;
      x1 = x1 + 1;
    }
    if (1 == x1) {
      x0[x2] = x3;
      x2 = 1;
      x3 = x0[0];
      x1 = x1 + 1;
    }
    if (2 == x1) {
      x0[x2] = x3;
      x2 = 4;
      x3 = x0[0] + 15;
      x1 = x1 + 1;
    }
    if (3 == x1) {
      x0[x2] = x3;
      x2 = 3;
      x3 = x0[0];
      x1 = x1 + 1;
    }
    if (4 == x1) {
      x0[x2] = x3;
      x2 = 3;
      x3 = x0[2] + x0[1];
      x1 = x1 + 1;
    }
    if (5 == x1) {
      x0[x2] = x3;
      x2 = 1;
      x3 = x0[2] + x0[0];
      x1 = x1 + 1;
    }
    if (6 == x1) {
      x0[x2] = x3;
      x2 = 2;
      x3 = x0[3] + x0[0];
      x1 = x1 + 1;
    }
    if (7 == x1) {
      x0[x2] = x3;
      x2 = 4;
      x3 = x0[4] + -1;
      x1 = x1 + 1;
    }
    if (8 == x1) {
      x0[x2] = x3;
      if (x0[4] != 0) x1 = x1 + -4;
      else x1 = x1 + 1;
    }
  }
  x0[x2] = x3;
  return x0;
}
/*****************************************
End of C Generated Code
*******************************************/
int main(int argc, char *argv[]) {
  int regfile[7] = {0, 0, 0, 0, 0, 0, 0};
  Snippet(regfile);
  if (regfile[0] != 0) {
    printf("error: regfile[0] = %d, expected 0\n", regfile[0]);
    return 1;
  }
  if (regfile[1] != 610) {
    printf("error: regfile[1] = %d, expected 610\n", regfile[1]);
    return 1;
  }
  if (regfile[2] != 987) {
    printf("error: regfile[2] = %d, expected 987\n", regfile[2]);
    return 1;
  }
  if (regfile[3] != 987) {
    printf("error: regfile[3] = %d, expected 987\n", regfile[3]);
    return 1;
  }
  if (regfile[4] != 0) {
    printf("error: regfile[4] = %d, expected 0\n", regfile[4]);
    return 1;
  }
  if (regfile[5] != 0) {
    printf("error: regfile[5] = %d, expected 0\n", regfile[5]);
    return 1;
  }
  if (regfile[6] != 0) {
    printf("error: regfile[6] = %d, expected 0\n", regfile[6]);
    return 1;
  }
  printf("OK\n");
  return 0;
}

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
  int x4 = 0;
  int x5 = 0;
  int x6 = 0;
  while (0 <= x1 && x1 < 3) {
    int x7 = x2;
    x1 = x7;
    x0[x3] = x5;
    int x8 = x4;
    x3 = x8;
    x5 = x6;
    if (0 == x7) if (!(x8 == 1 || x8 == 0) || x8 == 0) {
      x4 = 1;
      x6 = x0[0] + 3;
      x2 = x7 + 1;
    } else {
      x4 = 0;
      x6 = 0;
    }
    if (1 == x7) {
      bool x9 = x8 == 1;
      if (!(x9 || x9) || x8 == 0) {
        x4 = 1;
        x6 = x0[1] + -1;
        x2 = x7 + 1;
      } else {
        x4 = 0;
        x6 = 0;
      }
    }
    if (2 == x7) {
      if (x8 != 1) if (x0[1] == 0) x2 = x7 + 1;
      else x2 = x7 + -1;
      x4 = 0;
      x6 = 0;
    }
  }
  x0[x3] = x5;
  return x0;
}
/*****************************************
End of C Generated Code
*******************************************/
// cc file.c for execution
// cbmc -DCBMC file.c for verification
#ifndef CBMC
#define __CPROVER_assert(b,s) 0
#endif
int main(int argc, char *argv[]) {
  int regfile[7] = {0, 0, 0, 0, 0, 0, 0};
  Snippet(regfile);
  __CPROVER_assert(regfile[0]==0, "failure 0");
  if (regfile[0] != 0) {
    printf("error: regfile[0] = %d, expected 0\n", regfile[0]);
    goto error;
  }
  __CPROVER_assert(regfile[1]==0, "failure 1");
  if (regfile[1] != 0) {
    printf("error: regfile[1] = %d, expected 0\n", regfile[1]);
    goto error;
  }
  __CPROVER_assert(regfile[2]==0, "failure 2");
  if (regfile[2] != 0) {
    printf("error: regfile[2] = %d, expected 0\n", regfile[2]);
    goto error;
  }
  __CPROVER_assert(regfile[3]==0, "failure 3");
  if (regfile[3] != 0) {
    printf("error: regfile[3] = %d, expected 0\n", regfile[3]);
    goto error;
  }
  __CPROVER_assert(regfile[4]==0, "failure 4");
  if (regfile[4] != 0) {
    printf("error: regfile[4] = %d, expected 0\n", regfile[4]);
    goto error;
  }
  __CPROVER_assert(regfile[5]==0, "failure 5");
  if (regfile[5] != 0) {
    printf("error: regfile[5] = %d, expected 0\n", regfile[5]);
    goto error;
  }
  __CPROVER_assert(regfile[6]==0, "failure 6");
  if (regfile[6] != 0) {
    printf("error: regfile[6] = %d, expected 0\n", regfile[6]);
    goto error;
  }
  printf("OK\n");
  return 0;
  error:
  printf("\nRegfile:\n");
  for (int i = 0; i < 6; i++) {
    printf("%d ", regfile[i]);
  }
  printf("\nexpected:\n");
  printf("0 0 0 0 0 0 0  ");
  printf("\n\nFAILED\n");
  return 1;
}

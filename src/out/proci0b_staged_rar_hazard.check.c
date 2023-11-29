/*****************************************
Emitting C Generated Code
*******************************************/
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
/**************** Snippet ****************/
int* Snippet(int* x0) {
  char* x1 = "entry";
  bool x2 = false;
  int x3 = 0;
  int x4 = 0;
  int x5 = 0;
  int x6 = 0;
  while (!x2) {
    char* x7 = x1;
    if (strcmp("entry", x7) == 0) {
      if (!(x3 == 2 || x3 == 1) || x3 == 0) {
        x4 = 2;
        x6 = x0[1] + 1;
      } else {
        x4 = 0;
        x6 = 0;
      }
      x0[x3] = x5;
      int x8 = x4;
      x3 = x8;
      int x9 = x6;
      x5 = x9;
      if (!(x8 == 4 || x8 == 1) || x8 == 0) {
        x4 = 4;
        x6 = x0[1] + 2;
      } else {
        x4 = 0;
        x6 = 0;
      }
      x0[x8] = x9;
      int x10 = x4;
      x3 = x10;
      int x11 = x6;
      x5 = x11;
      if (!(x10 == 3 || x10 == 5) || x10 == 0) {
        x4 = 3;
        x6 = x0[5] + 3;
      } else {
        x4 = 0;
        x6 = 0;
      }
      x0[x10] = x11;
      int x12 = x4;
      x3 = x12;
      int x13 = x6;
      x5 = x13;
      x1 = "exit";
      x0[x12] = x13;
      x3 = x4;
      x5 = x6;
    }
    if (strcmp("exit", x7) == 0) x2 = true;
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
  __CPROVER_assert(regfile[2]==1, "failure 2");
  if (regfile[2] != 1) {
    printf("error: regfile[2] = %d, expected 1\n", regfile[2]);
    goto error;
  }
  __CPROVER_assert(regfile[3]==3, "failure 3");
  if (regfile[3] != 3) {
    printf("error: regfile[3] = %d, expected 3\n", regfile[3]);
    goto error;
  }
  __CPROVER_assert(regfile[4]==2, "failure 4");
  if (regfile[4] != 2) {
    printf("error: regfile[4] = %d, expected 2\n", regfile[4]);
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
  printf("0 0 1 3 2 0 0  ");
  printf("\n\nFAILED\n");
  return 1;
}

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
      if (!(x3 == 1 || x3 == 0) || x3 == 0) {
        x4 = 1;
        x6 = x0[0] + 3;
      } else {
        x4 = 0;
        x6 = 0;
      }
      x0[x3] = x5;
      int x8 = x4;
      x3 = x8;
      int x9 = x6;
      x5 = x9;
      x1 = "loop";
      x0[x8] = x9;
      x3 = x4;
      x5 = x6;
    }
    if (strcmp("loop", x7) == 0) {
      bool x10 = false;
      if (!(x3 == 1 || x3 == 1) || x3 == 0) {
        x4 = 1;
        x6 = x0[1] + -1;
      } else {
        x4 = 0;
        x6 = 0;
      }
      x1 = x7;
      x0[x3] = x5;
      int x11 = x4;
      x3 = x11;
      int x12 = x6;
      x5 = x12;
      if (!(x11 == 1)) if (x12 != 0) {
        x1 = "loop";
        x10 = true;
      } else x1 = x7;
      x4 = 0;
      x6 = 0;
      x0[x11] = x12;
      x3 = 0;
      x5 = 0;
      if (!x10) {
        x1 = "exit";
        x10 = true;
        x0[0] = 0;
        x3 = 0;
        x5 = 0;
      }
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

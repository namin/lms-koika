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
        x6 = x0[0] + 1;
      } else {
        x4 = 0;
        x6 = 0;
      }
      x0[x3] = x5;
      int x8 = x4;
      x3 = x8;
      int x9 = x6;
      x5 = x9;
      if (!(x8 == 2 || x8 == 1 || x8 == 1) || x8 == 0) {
        x4 = 2;
        x6 = x0[1] + x0[1];
      } else {
        x4 = 0;
        x6 = 0;
      }
      x0[x8] = x9;
      int x10 = x4;
      x3 = x10;
      int x11 = x6;
      x5 = x11;
      if (!(x10 == 3 || x10 == 2 || x10 == 1) || x10 == 0) {
        x4 = 3;
        x6 = x0[2] + x0[1];
      } else {
        x4 = 0;
        x6 = 0;
      }
      x0[x10] = x11;
      int x12 = x4;
      x3 = x12;
      int x13 = x6;
      x5 = x13;
      if (!(x12 == 4 || x12 == 3 || x12 == 2) || x12 == 0) {
        x4 = 4;
        x6 = x0[3] + x0[2];
      } else {
        x4 = 0;
        x6 = 0;
      }
      x0[x12] = x13;
      int x14 = x4;
      x3 = x14;
      int x15 = x6;
      x5 = x15;
      if (!(x14 == 1 || x14 == 4 || x14 == 3) || x14 == 0) {
        x4 = 1;
        x6 = x0[4] + x0[3];
      } else {
        x4 = 0;
        x6 = 0;
      }
      x0[x14] = x15;
      int x16 = x4;
      x3 = x16;
      int x17 = x6;
      x5 = x17;
      if (!(x16 == 2 || x16 == 1 || x16 == 4) || x16 == 0) {
        x4 = 2;
        x6 = x0[1] + x0[4];
      } else {
        x4 = 0;
        x6 = 0;
      }
      x0[x16] = x17;
      int x18 = x4;
      x3 = x18;
      int x19 = x6;
      x5 = x19;
      if (!(x18 == 3 || x18 == 2 || x18 == 1) || x18 == 0) {
        x4 = 3;
        x6 = x0[2] + x0[1];
      } else {
        x4 = 0;
        x6 = 0;
      }
      x0[x18] = x19;
      int x20 = x4;
      x3 = x20;
      int x21 = x6;
      x5 = x21;
      if (!(x20 == 4 || x20 == 3 || x20 == 2) || x20 == 0) {
        x4 = 4;
        x6 = x0[3] + x0[2];
      } else {
        x4 = 0;
        x6 = 0;
      }
      x0[x20] = x21;
      int x22 = x4;
      x3 = x22;
      int x23 = x6;
      x5 = x23;
      bool x24 = x22 == 4;
      if (!(x24 || x22 == 1 || x24) || x22 == 0) {
        x4 = 4;
        x6 = x0[1] + x0[4];
      } else {
        x4 = 0;
        x6 = 0;
      }
      x0[x22] = x23;
      int x25 = x4;
      x3 = x25;
      int x26 = x6;
      x5 = x26;
      x1 = "exit";
      x0[x25] = x26;
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
  __CPROVER_assert(regfile[1]==8, "failure 1");
  if (regfile[1] != 8) {
    printf("error: regfile[1] = %d, expected 8\n", regfile[1]);
    goto error;
  }
  __CPROVER_assert(regfile[2]==13, "failure 2");
  if (regfile[2] != 13) {
    printf("error: regfile[2] = %d, expected 13\n", regfile[2]);
    goto error;
  }
  __CPROVER_assert(regfile[3]==21, "failure 3");
  if (regfile[3] != 21) {
    printf("error: regfile[3] = %d, expected 21\n", regfile[3]);
    goto error;
  }
  __CPROVER_assert(regfile[4]==42, "failure 4");
  if (regfile[4] != 42) {
    printf("error: regfile[4] = %d, expected 42\n", regfile[4]);
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
  printf("0 8 13 21 42 0 0  ");
  printf("\n\nFAILED\n");
  return 1;
}

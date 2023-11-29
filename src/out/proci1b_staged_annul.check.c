/*****************************************
Emitting C Generated Code
*******************************************/
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
/**************** Snippet ****************/
int Snippet(int* x0) {
  int x1 = 0;
  int x2 = 0;
  int x3 = 0;
  int x4 = 0;
  int x5 = 0;
  int x6 = 0;
  int x7 = 137001;
  int x8 = 137012;
  int x9 = 0;
  int x10 = 0;
  int x11 = 0;
  int x12 = 0;
  int x13 = 0;
  int x14 = 0;
  while (x1 < 200 && (!(x11 == 0) || !(x9 == 0) || x2 < 4)) {
    int x15 = x3;
    x2 = x15;
    int x16 = x4;
    int x17 = x10;
    x9 = x17;
    int x18 = x8;
    int x19 = x12;
    x11 = x19;
    int x20 = x7;
    int x21 = x13;
    int x22 = x14;
    int x23 = x1 + 1;
    x1 = x23;
    bool x24 = x21 == 0;
    if (!x24) x0[x21] = x22;
    bool x25 = x20 == 137002;
    int x26 = x20 == 137001 ? x5 + x6 : (x20 == 137003 ? x5 - x6 : (x25 ? x5 * x6 : (x20 == 137004 ? (x5 == x6 ? 1 : 0) : (x20 == 137005 ? (x5 != x6 ? 1 : 0) : (x20 == 137006 ? (x5 < x6 ? 1 : 0) : (x20 == 137007 ? (x5 > x6 ? 1 : 0) : (x20 == 137008 ? (x5 <= x6 ? 1 : 0) : (x20 == 137009 ? (x5 >= x6 ? 1 : 0) : 0))))))));
    if (x25) if (x5 == 0 || x6 == 0) x1 = x23 + 1;
    else x1 = x23 + 7;
    x13 = x16;
    x14 = x26;
    bool x27 = false;
    if (4 == x15) {
      int x28 = x5;
      int x29 = x6;
      x4 = 0;
      x5 = 0;
      x10 = 0;
      x6 = 0;
      x8 = 137012;
      x12 = 0;
      x7 = 137001;
    }
    if (0 == x15) {
      x27 = !((!(x21 == 1 || x24) || x24) && (!(x16 == 1 || x16 == 0) || x16 == 0));
      x4 = 1;
      x5 = x0[0];
      x6 = 1;
      x7 = 137001;
      x8 = 137012;
      x10 = 1;
      x12 = x15;
      x3 = x15 + 1;
    }
    if (1 == x15) {
      x27 = !(x21 != 1 && x16 != 1);
      x4 = 0;
      x5 = x0[1];
      x6 = 0;
      x7 = 137005;
      x8 = 137011;
      x10 = 2;
      x12 = x15;
      x3 = x15 + 1;
    }
    if (2 == x15) {
      x27 = !((!(x21 == 2 || x24) || x24) && (!(x16 == 2 || x16 == 0) || x16 == 0));
      x4 = 2;
      x5 = x0[0];
      x6 = 2;
      x7 = 137001;
      x8 = 137012;
      x10 = 1;
      x12 = x15;
      x3 = x15 + 1;
    }
    if (3 == x15) {
      x27 = !((!(x21 == 3 || x24) || x24) && (!(x16 == 3 || x16 == 0) || x16 == 0));
      x4 = 3;
      x5 = x0[0];
      x6 = 3;
      x7 = 137001;
      x8 = 137012;
      x10 = 1;
      x12 = x15;
      x3 = x15 + 1;
    }
    if (x18 == 137012 ? false : (x26 == 0 ? x18 == 137010 : x26 == 1 && x18 == 137011)) {
      x3 = x26 == 0 ? x19 + 1 : (x26 == 1 ? x19 + x17 : x19 + 1);
      x4 = 0;
      x5 = 0;
      x10 = 0;
      x6 = 0;
      x8 = 137012;
      x12 = 0;
      x7 = 137001;
    } else if (x27) {
      x3 = x15;
      x4 = 0;
      x5 = 0;
      x10 = 0;
      x6 = 0;
      x8 = 137012;
      x12 = 0;
      x7 = 137001;
    }
  }
  int x30 = x4;
  int x31 = x7;
  int x32 = x13;
  int x33 = x1 + 1;
  x1 = x33;
  if (!(x32 == 0)) x0[x32] = x14;
  bool x34 = x31 == 137002;
  if (x34) if (x5 == 0 || x6 == 0) x1 = x33 + 1;
  else x1 = x33 + 7;
  int x35 = x1 + 1;
  x1 = x35;
  if (!(x30 == 0)) x0[x30] = x31 == 137001 ? x5 + x6 : (x31 == 137003 ? x5 - x6 : (x34 ? x5 * x6 : (x31 == 137004 ? (x5 == x6 ? 1 : 0) : (x31 == 137005 ? (x5 != x6 ? 1 : 0) : (x31 == 137006 ? (x5 < x6 ? 1 : 0) : (x31 == 137007 ? (x5 > x6 ? 1 : 0) : (x31 == 137008 ? (x5 <= x6 ? 1 : 0) : (x31 == 137009 ? (x5 >= x6 ? 1 : 0) : 0))))))));
  if (x7 == 137002) if (x5 == 0 || x6 == 0) x1 = x35 + 1;
  else x1 = x35 + 7;
  return x1;
}
/*****************************************
End of C Generated Code
*******************************************/
// cc file.c for execution
// cbmc -DCBMC file.c for verification
#ifndef CBMC
#define __CPROVER_assert(b,s) 0
#define nondet_uint() 0
#define __CPROVER_assume(b) 0
#endif
int bounded(int low, int high) {
  int x = nondet_uint();
  __CPROVER_assume(low <= x && x <= high);
  return x;
}
int main(int argc, char *argv[]) {
  int input = bounded(0, 10);
  int regfile[11] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
  int regfile2[11] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ,0};
  regfile[1] = input;
  regfile2[1] = input;
  for (int i = 7; i < 11; i++) {
    regfile[i] = bounded(0, 10);
    regfile2[i] = bounded(0, 10);
  }
  int c1 = Snippet(regfile);
  int c2 = Snippet(regfile2);
  __CPROVER_assert(c1 == c2, "timing leak");
  #ifndef CBMC
  if (regfile[0] != 0) {
    printf("error: regfile[0] = %d, expected 0\n", regfile[0]);
    goto error;
  }
  if (regfile[1] != 1) {
    printf("error: regfile[1] = %d, expected 1\n", regfile[1]);
    goto error;
  }
  if (regfile[2] != 0) {
    printf("error: regfile[2] = %d, expected 0\n", regfile[2]);
    goto error;
  }
  if (regfile[3] != 3) {
    printf("error: regfile[3] = %d, expected 3\n", regfile[3]);
    goto error;
  }
  if (regfile[4] != 0) {
    printf("error: regfile[4] = %d, expected 0\n", regfile[4]);
    goto error;
  }
  if (regfile[5] != 0) {
    printf("error: regfile[5] = %d, expected 0\n", regfile[5]);
    goto error;
  }
  if (regfile[6] != 0) {
    printf("error: regfile[6] = %d, expected 0\n", regfile[6]);
    goto error;
  }
  if (regfile[7] != 0) {
    printf("error: regfile[7] = %d, expected 0\n", regfile[7]);
    goto error;
  }
  if (regfile[8] != 0) {
    printf("error: regfile[8] = %d, expected 0\n", regfile[8]);
    goto error;
  }
  if (regfile[9] != 0) {
    printf("error: regfile[9] = %d, expected 0\n", regfile[9]);
    goto error;
  }
  if (regfile[10] != 0) {
    printf("error: regfile[10] = %d, expected 0\n", regfile[10]);
    goto error;
  }
  printf("OK c1=%d\n", c1);
  return 0;
  error:
  printf("\nRegfile:\n");
  for (int i = 0; i < 11; i++) {
    printf("%d ", regfile[i]);
  }
  printf("\nexpected:\n");
  printf("0 1 0 3 0 0 0 0 0 0 0  ");
  printf("\n\nFAILED with tick count=%d\n", c1);
  #endif
  return 1;
}

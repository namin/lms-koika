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
  while (!x2) {
    if (strcmp("entry", x1) == 0) {
      x0[2] = x0[0] + 1;
      x0[1] = x0[0];
      x0[4] = x0[0] + 15;
      x0[3] = x0[0];
      x1 = "loop";
    }
    if (strcmp(x1, "exit") == 0) x2 = true;
    if (strcmp("loop", x1) == 0) {
      bool x3 = false;
      x0[3] = x0[2] + x0[1];
      x0[1] = x0[2] + x0[0];
      x0[2] = x0[3] + x0[0];
      int x4 = x0[4] + -1;
      x0[4] = x4;
      if (x4 != 0) {
        x1 = "loop";
        x3 = true;
      }
      if (!x3) {
        x1 = "exit";
        x3 = true;
      }
    }
    if (strcmp(x1, "exit") == 0) x2 = true;
    if (strcmp(x1, "exit") == 0) x2 = true;
  }
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

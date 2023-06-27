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
  int regfile[6] = {0, 0, 0, 0, 0, 0};
  Snippet(regfile);
  for (int i = 0; i < 6; i++) {
    printf("%d ", regfile[i]);
  }
  printf("\n");
  return 0;
}

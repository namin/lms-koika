/*****************************************
Emitting C Generated Code
*******************************************/
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
/*********** Datastructures ***********/
struct ProgramStateT {
  int* vars;
  int* mem;
};
/**************** Snippet ****************/
struct ProgramStateT Snippet(struct ProgramStateT x0) {
  int* x1 = x0.vars;
  int* x2 = x0.mem;
  x1[0] = 1;
  x1[1] = 1;
  while (x1[0] == 1 && x1[1] <= 5) {
    if (!(x2[x1[1]] == x2[x1[1] + 10])) x1[0] = 0;
    x1[1] = x1[1] + 1;
  }
  x0.vars = x1;
  x0.mem = x2;
  return x0;
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

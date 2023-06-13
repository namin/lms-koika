/*****************************************
Emitting C Generated Code
*******************************************/
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
/**************** Snippet ****************/
void Snippet(int* x0) {
  int x1 = 0;
  while (0 <= x1 && x1 < 2) {
    if (0 == x1) {
      x0[0] = x0[0] + x0[0];
      x1 = 1;
    }
    if (1 == x1) x1 = x0[0] == 0 ? 0 : 2;
  }
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

/*****************************************
Emitting C Generated Code
*******************************************/
#include <stdlib.h>
#include "state.h"
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
/**************** Snippet ****************/
lms.core.unknown Snippet(int* x0) {
  int x1 = x0[0];
  return x1 == 0 ? ({
    x0[0] = 1;
    x0[6] = x0[6] + x0[6];
    x1 == 1 ? ({
      x0[0] = 2;
      x0[6] == 0 ? ({
        x0[0] = 0;
        exit(x0);
      }) : exit(x0);
    }) : exit(x0);
  }) : (x1 == 1 ? ({
    x0[0] = 2;
    x0[6] == 0 ? ({
      x0[0] = 0;
      exit(x0);
    }) : exit(x0);
  }) : exit(x0));
}
/*****************************************
End of C Generated Code
*******************************************/
int main(int argc, char *argv[]) {
  if (argc != 2) {
    printf("usage: %s <arg>\n", argv[0]);
    return 0;
  }
  Snippet();
  return 0;
}

/*****************************************
Emitting C Generated Code
*******************************************/
#include <stdlib.h>
#include "state.h"
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
/**************** Snippet ****************/
lms.core.unknown Snippet(int x0) {
  return exit(x0);
}
/*****************************************
End of C Generated Code
*******************************************/
int main(int argc, char *argv[]) {
  if (argc != 2) {
    printf("usage: %s <arg>\n", argv[0]);
    return 0;
  }
  Snippet(atoi(argv[1]));
  return 0;
}

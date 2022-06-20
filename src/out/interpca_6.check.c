/*****************************************
Emitting C Generated Code
*******************************************/
#include <stdlib.h>
#include "state.h"
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
/**************** Snippet ****************/
int* Snippet(int* x0) {
  x0[0] = 0;
  if (x0[2] == 0) {
    x0[2] = 1;
    x0[5] = x0[1];
    int x1 = state_btb(x0);
    x0[3] = x0[0];
    x0[4] = x1;
    x0[0] = x1;
  }
  if (x0[2] == 1) if (x0[5] == x0[1]) {
    int x2 = x0[3];
    int x3 = x0[4];
    x0[2] = 0;
    if (x2 == 0) {
      x0[6] = x0[6] + x0[6];
      if (x3 != 1) {
        x0[0] = 1;
        x0[1] = ~(x0[1]);
      }
    }
    if (x2 == 1) {
      set_state_btb(x0, x0[6], 1);
      if (x0[6] == 0) if (x3 != 0) {
        x0[0] = 0;
        x0[1] = ~(x0[1]);
      }
      else if (x3 != 2) {
        x0[0] = 2;
        x0[1] = ~(x0[1]);
      }
    }
  } else x0[2] = 0;
  if (x0[2] == 0) {
    x0[2] = 1;
    x0[5] = x0[1];
    int x4 = state_btb(x0);
    x0[3] = x0[0];
    x0[4] = x4;
    x0[0] = x4;
  }
  if (x0[2] == 1) if (x0[5] == x0[1]) {
    int x5 = x0[3];
    int x6 = x0[4];
    x0[2] = 0;
    if (x5 == 0) {
      x0[6] = x0[6] + x0[6];
      if (x6 != 1) {
        x0[0] = 1;
        x0[1] = ~(x0[1]);
      }
    }
    if (x5 == 1) {
      set_state_btb(x0, x0[6], 1);
      if (x0[6] == 0) if (x6 != 0) {
        x0[0] = 0;
        x0[1] = ~(x0[1]);
      }
      else if (x6 != 2) {
        x0[0] = 2;
        x0[1] = ~(x0[1]);
      }
    }
  } else x0[2] = 0;
  if (x0[2] == 0) {
    x0[2] = 1;
    x0[5] = x0[1];
    int x7 = state_btb(x0);
    x0[3] = x0[0];
    x0[4] = x7;
    x0[0] = x7;
  }
  if (x0[2] == 1) if (x0[5] == x0[1]) {
    int x8 = x0[3];
    int x9 = x0[4];
    x0[2] = 0;
    if (x8 == 0) {
      x0[6] = x0[6] + x0[6];
      if (x9 != 1) {
        x0[0] = 1;
        x0[1] = ~(x0[1]);
      }
    }
    if (x8 == 1) {
      set_state_btb(x0, x0[6], 1);
      if (x0[6] == 0) if (x9 != 0) {
        x0[0] = 0;
        x0[1] = ~(x0[1]);
      }
      else if (x9 != 2) {
        x0[0] = 2;
        x0[1] = ~(x0[1]);
      }
    }
  } else x0[2] = 0;
  if (x0[2] == 0) {
    x0[2] = 1;
    x0[5] = x0[1];
    int x10 = state_btb(x0);
    x0[3] = x0[0];
    x0[4] = x10;
    x0[0] = x10;
  }
  if (x0[2] == 1) if (x0[5] == x0[1]) {
    int x11 = x0[3];
    int x12 = x0[4];
    x0[2] = 0;
    if (x11 == 0) {
      x0[6] = x0[6] + x0[6];
      if (x12 != 1) {
        x0[0] = 1;
        x0[1] = ~(x0[1]);
      }
    }
    if (x11 == 1) {
      set_state_btb(x0, x0[6], 1);
      if (x0[6] == 0) if (x12 != 0) {
        x0[0] = 0;
        x0[1] = ~(x0[1]);
      }
      else if (x12 != 2) {
        x0[0] = 2;
        x0[1] = ~(x0[1]);
      }
    }
  } else x0[2] = 0;
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
  Snippet();
  return 0;
}

// Copyright Stefan Höck

#include <stdio.h>
#include <uv.h>

int main(void) {
  printf("toCode Default = %d\n", UV_RUN_DEFAULT);
  printf("toCode Once = %d\n", UV_RUN_ONCE);
  printf("toCode NoWait = %d\n", UV_RUN_NOWAIT);
}

// Copyright Stefan Höck

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <uv.h>

char uv_ready(char *p){return p[0];}

void uv_clear_ready(char *p){p[0] = 0;}

void uv_set_ready(char *p){p[0] = 1;}

void *uv_fs_cleanup(uv_fs_t *req) {
  uv_fs_req_cleanup(req);
  free(req);
}

void idris_write_cb(uv_fs_t *req) {
    char *p = req->data;
    p[0] = 1;
    uv_fs_cleanup(req);
}

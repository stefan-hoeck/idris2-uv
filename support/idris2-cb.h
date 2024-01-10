// Copyright Stefan Höck

#ifndef SUPPORT_IDRIS2_UV_H_
#define SUPPORT_IDRIS2_UV_H_

void *uv_fs_cleanup(uv_fs_t *req);

void idris_write_cb(uv_fs_t *req);

void idris_read_cb(uv_fs_t *req);

char uv_ready(char *p);

void uv_clear_ready(char *p);

void uv_set_ready(char *p);

#endif // SUPPORT_IDRIS2_UV_H_

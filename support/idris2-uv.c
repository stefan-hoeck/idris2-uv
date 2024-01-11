// Copyright Stefan Höck

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <uv.h>

void *uv_set_buf_len(uv_buf_t *buf, unsigned int length) { buf->len = length; }

unsigned int uv_get_buf_len(uv_buf_t *buf) { return buf->len; }

char *uv_get_buf_base(uv_buf_t *buf) { return buf->base; }

void *uv_set_buf_base(uv_buf_t *buf, char *dat) { buf->base = dat; }

void *uv_copy_buf(char *src, char *dest, int len) { memcpy(dest, src, len); }

int idris_uv_write(uv_write_t *wr, uv_stream_t *str, char *data,
                   unsigned int size, uv_write_cb cb) {
  uv_buf_t buf = uv_buf_init(data, size);
  return uv_write(wr, str, &buf, 1, cb);
}

int idris_uv_fs_write(uv_loop_t *loop, uv_fs_t *req, uv_file file, char *data,
                      unsigned int size, int64_t offset, uv_fs_cb cb) {
  uv_buf_t buf = uv_buf_init(data, size);
  return uv_fs_write(loop, req, file, &buf, 1, offset, cb);
}

int idris_uv_fs_read(uv_loop_t *loop, uv_fs_t *req, uv_file file, char *data,
                     unsigned int size, int64_t offset, uv_fs_cb cb) {
  uv_buf_t buf = uv_buf_init(data, size);
  return uv_fs_read(loop, req, file, &buf, 1, offset, cb);
}

// `addrinfo` setters and getters
void *uv_set_ai_family(struct addrinfo *info, int family) {
  info->ai_family = family;
}

void *uv_set_ai_socktype(struct addrinfo *info, int socktype) {
  info->ai_socktype = socktype;
}

void *uv_set_ai_protocol(struct addrinfo *info, int protocol) {
  info->ai_protocol = protocol;
}

void *uv_set_ai_flags(struct addrinfo *info, int flags) {
  info->ai_flags = flags;
}

int uv_get_ai_family(struct addrinfo *info) { return info->ai_family; }

int uv_get_ai_socktype(struct addrinfo *info) { return info->ai_socktype; }

int uv_get_ai_protocol(struct addrinfo *info) { return info->ai_protocol; }

int uv_get_ai_flags(struct addrinfo *info) { return info->ai_flags; }

struct sockaddr *uv_get_ai_addr(struct addrinfo *i) {return i->ai_addr;}

uint64_t uv_get_st_dev(uv_stat_t *stat) { return stat->st_dev; }

uint64_t uv_get_st_mode(uv_stat_t *stat) { return stat->st_mode; }

uint64_t uv_get_st_nlink(uv_stat_t *stat) { return stat->st_nlink; }

uint64_t uv_get_st_uid(uv_stat_t *stat) { return stat->st_uid; }

uint64_t uv_get_st_gid(uv_stat_t *stat) { return stat->st_gid; }

uint64_t uv_get_st_rdev(uv_stat_t *stat) { return stat->st_rdev; }

uint64_t uv_get_st_ino(uv_stat_t *stat) { return stat->st_ino; }

uint64_t uv_get_st_size(uv_stat_t *stat) { return stat->st_size; }

uint64_t uv_get_st_blksize(uv_stat_t *stat) { return stat->st_blksize; }

uint64_t uv_get_st_blocks(uv_stat_t *stat) { return stat->st_blocks; }

uint64_t uv_get_st_flags(uv_stat_t *stat) { return stat->st_flags; }

uint64_t uv_get_st_gen(uv_stat_t *stat) { return stat->st_gen; }

uv_timespec_t uv_get_st_atim(uv_stat_t *stat) { return stat->st_atim; }

uv_timespec_t uv_get_st_mtim(uv_stat_t *stat) { return stat->st_mtim; }

uv_timespec_t uv_get_st_ctim(uv_stat_t *stat) { return stat->st_ctim; }

uv_timespec_t uv_get_st_birthtim(uv_stat_t *stat) { return stat->st_birthtim; }

uv_dirent_t *uv_dirents(uv_dir_t *dir) { return dir->dirents; }

ssize_t uv_nentries(uv_dir_t *dir) { return dir->nentries; }

const char *uv_fs_get_dirent_name(uv_dirent_t *dirent) { return dirent->name; }

int uv_fs_get_dirent_type(uv_dirent_t *dirent) { return dirent->type; }

uint64_t uv_get_f_type(uv_statfs_t *stat) { return stat->f_type; }

uint64_t uv_get_f_bsize(uv_statfs_t *stat) { return stat->f_bsize; }

uint64_t uv_get_f_blocks(uv_statfs_t *stat) { return stat->f_blocks; }

uint64_t uv_get_f_bfree(uv_statfs_t *stat) { return stat->f_bfree; }

uint64_t uv_get_f_bavail(uv_statfs_t *stat) { return stat->f_bavail; }

uint64_t uv_get_f_files(uv_statfs_t *stat) { return stat->f_files; }

uint64_t uv_get_f_ffree(uv_statfs_t *stat) { return stat->f_ffree; }

int64_t uv_get_tv_sec(uv_timespec_t time) { return time.tv_sec; }

int64_t uv_get_tv_nsec(uv_timespec_t time) { return time.tv_nsec; }

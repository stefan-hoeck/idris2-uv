// Copyright Stefan Höck

#ifndef SUPPORT_IDRIS2_UV_H_
#define SUPPORT_IDRIS2_UV_H_

char *uv_get_buf_base(uv_buf_t *buf);

unsigned int uv_get_buf_len(uv_buf_t *buf);

void *uv_set_buf_base(uv_buf_t *buf, char *dat);

void *uv_set_buf_len(uv_buf_t *buf, unsigned int length);

void *uv_copy_buf(char *src, char *dest, int len);

void *uv_init_buf(uv_buf_t *buf, char *base, unsigned int len);

int idris_uv_fs_write(uv_loop_t *loop, uv_fs_t *req, uv_file file, char *data,
                     unsigned int size, int64_t offset, uv_fs_cb cb);

// `addrinfo` setters and getters
void *uv_set_ai_family(struct addrinfo *info, int family);

void *uv_set_ai_socktype(struct addrinfo *info, int socktype);

void *uv_set_ai_protocol(struct addrinfo *info, int protocol);

void *uv_set_ai_flags(struct addrinfo *info, int flags);

int uv_get_ai_family(struct addrinfo *info);

int uv_get_ai_socktype(struct addrinfo *info);

int uv_get_ai_protocol(struct addrinfo *info);

int uv_get_ai_flags(struct addrinfo *info);

struct sockaddr *uv_get_ai_addr(struct addrinfo *info);

// uv_stat_t accessors

uint64_t uv_get_st_dev(uv_stat_t *stat);

uint64_t uv_get_st_mode(uv_stat_t *stat);

uint64_t uv_get_st_nlink(uv_stat_t *stat);

uint64_t uv_get_st_uid(uv_stat_t *stat);

uint64_t uv_get_st_gid(uv_stat_t *stat);

uint64_t uv_get_st_rdev(uv_stat_t *stat);

uint64_t uv_get_st_ino(uv_stat_t *stat);

uint64_t uv_get_st_size(uv_stat_t *stat);

uint64_t uv_get_st_blksize(uv_stat_t *stat);

uint64_t uv_get_st_blocks(uv_stat_t *stat);

uint64_t uv_get_st_flags(uv_stat_t *stat);

uint64_t uv_get_st_gen(uv_stat_t *stat);

uv_timespec_t uv_get_st_atim(uv_stat_t *stat);

uv_timespec_t uv_get_st_mtim(uv_stat_t *stat);

uv_timespec_t uv_get_st_ctim(uv_stat_t *stat);

uv_timespec_t uv_get_st_birthtim(uv_stat_t *stat);

uv_dirent_t *uv_dirents(uv_dir_t *dir);

ssize_t uv_nentries(uv_dir_t *dir);

const char *uv_fs_get_dirent_name(uv_dirent_t *dirent);

int uv_fs_get_dirent_type(uv_dirent_t *dirent);

uint64_t uv_get_f_type(uv_statfs_t *stat);

uint64_t uv_get_f_bsize(uv_statfs_t *stat);

uint64_t uv_get_f_blocks(uv_statfs_t *stat);

uint64_t uv_get_f_bfree(uv_statfs_t *stat);

uint64_t uv_get_f_bavail(uv_statfs_t *stat);

uint64_t uv_get_f_files(uv_statfs_t *stat);

uint64_t uv_get_f_ffree(uv_statfs_t *stat);

int64_t uv_get_tv_sec(uv_timespec_t time);

int64_t uv_get_tv_nsec(uv_timespec_t time);

int uv_queue_work_idris(uv_loop_t *loop, uv_work_t *req, uv_work_cb work_cb, uv_after_work_cb after_work_cb);

#endif // SUPPORT_IDRIS2_UV_H_

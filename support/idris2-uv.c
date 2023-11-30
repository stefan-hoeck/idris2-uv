// Copyright Stefan Höck

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <uv.h>

uv_buf_t uv_deref_buf(uv_buf_t *ptr) { return *ptr; }

void *uv_set_buf_len(uv_buf_t *buf, unsigned int length) { buf->len = length; }

unsigned int uv_get_buf_len(uv_buf_t *buf) { return buf->len; }

char *uv_get_buf_base(uv_buf_t *buf) { return buf->base; }

void *uv_set_buf_base(uv_buf_t *buf, char *dat) { buf->base = dat; }

void *uv_copy_buf(char *src, char *dest, int len) { memcpy(dest, src, len); }

int uv_fs_close_sync(uv_loop_t *loop, uv_file file) {
  uv_fs_t req;
  return uv_fs_close(loop, &req, file, NULL);
}

int uv_fs_open_sync(uv_loop_t *loop, uv_fs_t *req, const char *path, int flags,
                    int mode) {
  return uv_fs_open(loop, req, path, flags, mode, NULL);
}

void *uv_close_sync(uv_handle_t *handle) { uv_close(handle, NULL); }

int uv_fs_write_sync(uv_loop_t *loop, uv_file file, const uv_buf_t bufs[],
                     unsigned int nbufs, int64_t offset) {
  uv_fs_t req;
  int res = uv_fs_write(loop, &req, file, bufs, nbufs, offset, NULL);
  uv_fs_req_cleanup(&req);
  return res;
}

void *uv_init_buf(uv_buf_t *buf, char *base, unsigned int len) {
  *buf = uv_buf_init(base, len);
  return buf;
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

struct sockaddr *uv_get_ai_addr(struct addrinfo *info) {
  return info->ai_addr;
}

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

int uv_dirent_unknown() { return UV_DIRENT_UNKNOWN; }
int uv_dirent_file() { return UV_DIRENT_FILE; }
int uv_dirent_dir() { return UV_DIRENT_DIR; }
int uv_dirent_link() { return UV_DIRENT_LINK; }
int uv_dirent_fifo() { return UV_DIRENT_FIFO; }
int uv_dirent_socket() { return UV_DIRENT_SOCKET; }
int uv_dirent_char() { return UV_DIRENT_CHAR; }
int uv_dirent_block() { return UV_DIRENT_BLOCK; }

int uv_sigabrt() { return SIGABRT; }
int uv_sigfpe() { return SIGFPE; }
int uv_sighup() { return SIGHUP; }
int uv_sigill() { return SIGILL; }
int uv_sigint() { return SIGINT; }
int uv_sigquit() { return SIGQUIT; }
int uv_sigsegv() { return SIGSEGV; }
int uv_sigtrap() { return SIGTRAP; }
int uv_sigusr1() { return SIGUSR1; }
int uv_sigusr2() { return SIGUSR2; }

int uv_rdonly() { return O_RDONLY; }
int uv_wronly() { return O_WRONLY; }
int uv_rdwr() { return O_RDWR; }
int uv_append() { return O_APPEND; }
int uv_creat() { return O_CREAT; }

int uv_s_irwxu() { return S_IRWXU; }
int uv_s_irusr() { return S_IRUSR; }
int uv_s_iwusr() { return S_IWUSR; }
int uv_s_ixusr() { return S_IXUSR; }
int uv_s_irwxg() { return S_IRWXG; }
int uv_s_irgrp() { return S_IRGRP; }
int uv_s_iwgrp() { return S_IWGRP; }
int uv_s_ixgrp() { return S_IXGRP; }
int uv_s_irwxo() { return S_IRWXO; }
int uv_s_iroth() { return S_IROTH; }
int uv_s_iwoth() { return S_IWOTH; }
int uv_s_ixoth() { return S_IXOTH; }

size_t uv_async_sz() { return uv_handle_size(UV_ASYNC); }
size_t uv_check_sz() { return uv_handle_size(UV_CHECK); }
size_t uv_fs_event_sz() { return uv_handle_size(UV_FS_EVENT); }
size_t uv_fs_poll_sz() { return uv_handle_size(UV_FS_POLL); }
size_t uv_handle_sz() { return uv_handle_size(UV_HANDLE); }
size_t uv_idle_sz() { return uv_handle_size(UV_IDLE); }
size_t uv_named_pipe_sz() { return uv_handle_size(UV_NAMED_PIPE); }
size_t uv_poll_sz() { return uv_handle_size(UV_POLL); }
size_t uv_prepare_sz() { return uv_handle_size(UV_PREPARE); }
size_t uv_process_sz() { return uv_handle_size(UV_PROCESS); }
size_t uv_stream_sz() { return uv_handle_size(UV_STREAM); }
size_t uv_tcp_sz() { return uv_handle_size(UV_TCP); }
size_t uv_timer_sz() { return uv_handle_size(UV_TIMER); }
size_t uv_tty_sz() { return uv_handle_size(UV_TTY); }
size_t uv_udp_sz() { return uv_handle_size(UV_UDP); }
size_t uv_signal_sz() { return uv_handle_size(UV_SIGNAL); }

size_t uv_req_sz() { return uv_req_size(UV_REQ); }
size_t uv_connect_sz() { return uv_req_size(UV_CONNECT); }
size_t uv_write_sz() { return uv_req_size(UV_WRITE); }
size_t uv_shutdown_sz() { return uv_req_size(UV_SHUTDOWN); }
size_t uv_udp_send_sz() { return uv_req_size(UV_UDP_SEND); }
size_t uv_fs_sz() { return uv_req_size(UV_FS); }
size_t uv_work_sz() { return uv_req_size(UV_WORK); }
size_t uv_getaddrinfo_sz() { return uv_req_size(UV_GETADDRINFO); }
size_t uv_getnameinfo_sz() { return uv_req_size(UV_GETNAMEINFO); }

size_t uv_buf_sz() { return sizeof(uv_buf_t); }
size_t uv_loop_sz() { return sizeof(uv_loop_t); }
size_t uv_sockaddr_in_sz() { return sizeof(struct sockaddr_in); }
size_t uv_sockaddr_in6_sz() { return sizeof(struct sockaddr_in6); }
size_t uv_sockaddr_sz() { return sizeof(struct sockaddr); }
size_t uv_addrinfo_sz() { return sizeof(struct addrinfo); }

int uv_af_inet() { return AF_INET; }
int uv_af_inet6() { return AF_INET6; }
int uv_af_unix() { return AF_UNIX; }
int uv_af_unspec() { return AF_UNSPEC; }
int uv_sock_stream() { return SOCK_STREAM; }
int uv_sock_dgram() { return SOCK_DGRAM; }
int uv_sock_raw() { return SOCK_RAW; }
int uv_sock_any() { return 0; }
int uv_ipproto_ip() { return IPPROTO_IP; }
int uv_ipproto_ipv6() { return IPPROTO_IPV6; }
int uv_ipproto_icmp() { return IPPROTO_ICMP; }
int uv_ipproto_raw() { return IPPROTO_RAW; }
int uv_ipproto_tcp() { return IPPROTO_TCP; }
int uv_ipproto_udp() { return IPPROTO_UDP; }

int uv_run_default() { return UV_RUN_DEFAULT; }
int uv_run_once() { return UV_RUN_ONCE; }
int uv_run_nowait() { return UV_RUN_NOWAIT; }

// Error codes
int uv_e2big(){ return UV_E2BIG; }
int uv_eacces(){ return UV_EACCES; }
int uv_eaddrinuse(){ return UV_EADDRINUSE; }
int uv_eaddrnotavail(){ return UV_EADDRNOTAVAIL; }
int uv_eafnosupport(){ return UV_EAFNOSUPPORT; }
int uv_eagain(){ return UV_EAGAIN; }
int uv_eai_addrfamily(){ return UV_EAI_ADDRFAMILY; }
int uv_eai_again(){ return UV_EAI_AGAIN; }
int uv_eai_badflags(){ return UV_EAI_BADFLAGS; }
int uv_eai_badhints(){ return UV_EAI_BADHINTS; }
int uv_eai_canceled(){ return UV_EAI_CANCELED; }
int uv_eai_fail(){ return UV_EAI_FAIL; }
int uv_eai_family(){ return UV_EAI_FAMILY; }
int uv_eai_memory(){ return UV_EAI_MEMORY; }
int uv_eai_nodata(){ return UV_EAI_NODATA; }
int uv_eai_noname(){ return UV_EAI_NONAME; }
int uv_eai_overflow(){ return UV_EAI_OVERFLOW; }
int uv_eai_protocol(){ return UV_EAI_PROTOCOL; }
int uv_eai_service(){ return UV_EAI_SERVICE; }
int uv_eai_socktype(){ return UV_EAI_SOCKTYPE; }
int uv_ealready(){ return UV_EALREADY; }
int uv_ebadf(){ return UV_EBADF; }
int uv_ebusy(){ return UV_EBUSY; }
int uv_ecanceled(){ return UV_ECANCELED; }
int uv_echarset(){ return UV_ECHARSET; }
int uv_econnaborted(){ return UV_ECONNABORTED; }
int uv_econnrefused(){ return UV_ECONNREFUSED; }
int uv_econnreset(){ return UV_ECONNRESET; }
int uv_edestaddrreq(){ return UV_EDESTADDRREQ; }
int uv_eexist(){ return UV_EEXIST; }
int uv_efault(){ return UV_EFAULT; }
int uv_efbig(){ return UV_EFBIG; }
int uv_ehostunreach(){ return UV_EHOSTUNREACH; }
int uv_eintr(){ return UV_EINTR; }
int uv_einval(){ return UV_EINVAL; }
int uv_eio(){ return UV_EIO; }
int uv_eisconn(){ return UV_EISCONN; }
int uv_eisdir(){ return UV_EISDIR; }
int uv_eloop(){ return UV_ELOOP; }
int uv_emfile(){ return UV_EMFILE; }
int uv_emsgsize(){ return UV_EMSGSIZE; }
int uv_enametoolong(){ return UV_ENAMETOOLONG; }
int uv_enetdown(){ return UV_ENETDOWN; }
int uv_enetunreach(){ return UV_ENETUNREACH; }
int uv_enfile(){ return UV_ENFILE; }
int uv_enobufs(){ return UV_ENOBUFS; }
int uv_enodev(){ return UV_ENODEV; }
int uv_enoent(){ return UV_ENOENT; }
int uv_enomem(){ return UV_ENOMEM; }
int uv_enonet(){ return UV_ENONET; }
int uv_enoprotoopt(){ return UV_ENOPROTOOPT; }
int uv_enospc(){ return UV_ENOSPC; }
int uv_enosys(){ return UV_ENOSYS; }
int uv_enotconn(){ return UV_ENOTCONN; }
int uv_enotdir(){ return UV_ENOTDIR; }
int uv_enotempty(){ return UV_ENOTEMPTY; }
int uv_enotsock(){ return UV_ENOTSOCK; }
int uv_enotsup(){ return UV_ENOTSUP; }
int uv_eoverflow(){ return UV_EOVERFLOW; }
int uv_eperm(){ return UV_EPERM; }
int uv_epipe(){ return UV_EPIPE; }
int uv_eproto(){ return UV_EPROTO; }
int uv_eprotonosupport(){ return UV_EPROTONOSUPPORT; }
int uv_eprototype(){ return UV_EPROTOTYPE; }
int uv_erange(){ return UV_ERANGE; }
int uv_erofs(){ return UV_EROFS; }
int uv_eshutdown(){ return UV_ESHUTDOWN; }
int uv_espipe(){ return UV_ESPIPE; }
int uv_esrch(){ return UV_ESRCH; }
int uv_etimedout(){ return UV_ETIMEDOUT; }
int uv_etxtbsy(){ return UV_ETXTBSY; }
int uv_exdev(){ return UV_EXDEV; }
int uv_unknown(){ return UV_UNKNOWN; }
int uv_eof(){ return UV_EOF; }
int uv_enxio(){ return UV_ENXIO; }
int uv_emlink(){ return UV_EMLINK; }
int uv_enotty(){ return UV_ENOTTY; }
int uv_eftype(){ return UV_EFTYPE; }
int uv_eilseq(){ return UV_EILSEQ; }
int uv_esocktnosupport(){ return UV_ESOCKTNOSUPPORT; }
int uv_eunatch(){ return UV_EUNATCH; }

// Copyright Stefan Höck

uv_buf_t uv_deref_buf(uv_buf_t *ptr);

char *uv_get_buf_base(uv_buf_t *buf);

unsigned int *uv_get_buf_len(uv_buf_t *buf);

void *uv_set_buf_base(uv_buf_t *buf, char *dat);

void *uv_set_buf_len(uv_buf_t *buf, unsigned int length);

void *uv_copy_buf(char *src, char *dest, int len);

void *uv_init_buf(uv_buf_t *buf, char *base, unsigned int len);

void *uv_close_sync(uv_handle_t *handle);

int uv_fs_close_sync(uv_loop_t *loop, uv_file file);

int uv_fs_open_sync(uv_loop_t *loop, uv_fs_t *req, const char *path, int flags,
                    int mode);

int uv_fs_write_sync(uv_loop_t *loop, uv_file file, const uv_buf_t bufs[],
                     unsigned int nbufs, int64_t offset);

int uv_EOF();

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

// dirent type
int uv_dirent_unknown();

int uv_dirent_file();

int uv_dirent_dir();

int uv_dirent_link();

int uv_dirent_fifo();

int uv_dirent_socket();

int uv_dirent_char();

int uv_dirent_block();

// Signal Codes
int uv_sigabrt();
int uv_sigfpe();
int uv_sighup();
int uv_sigill();
int uv_sigint();
int uv_sigquit();
int uv_sigsegv();
int uv_sigtrap();
int uv_sigusr1();
int uv_sigusr2();

// File opening flags
int uv_rdonly();
int uv_wronly();
int uv_rdwr();
int uv_append();
int uv_creat();

// File creation modes
int uv_s_irwxu();
int uv_s_irusr();
int uv_s_iwusr();
int uv_s_ixusr();
int uv_s_irwxg();
int uv_s_irgrp();
int uv_s_iwgrp();
int uv_s_ixgrp();
int uv_s_irwxo();
int uv_s_iroth();
int uv_s_iwoth();
int uv_s_ixoth();

// Handle types
size_t uv_async_sz();
size_t uv_check_sz();
size_t uv_fs_event_sz();
size_t uv_fs_poll_sz();
size_t uv_handle_sz();
size_t uv_idle_sz();
size_t uv_named_pipe_sz();
size_t uv_poll_sz();
size_t uv_prepare_sz();
size_t uv_process_sz();
size_t uv_stream_sz();
size_t uv_tcp_sz();
size_t uv_timer_sz();
size_t uv_tty_sz();
size_t uv_udp_sz();
size_t uv_signal_sz();

// Request types
size_t uv_req_sz();
size_t uv_connect_sz();
size_t uv_write_sz();
size_t uv_shutdown_sz();
size_t uv_udp_send_sz();
size_t uv_fs_sz();
size_t uv_work_sz();
size_t uv_getaddrinfo_sz();
size_t uv_getnameinfo_sz();

// Size of uv_buf and loop struct
size_t uv_buf_sz();
size_t uv_loop_sz();

// addrinfo constants
size_t uv_addrinfo_sz();
size_t uv_sockaddr_in_sz();
size_t uv_sockaddr_in6_sz();
size_t uv_sockaddr_sz();

// ai_family constants
int uv_af_inet();
int uv_af_inet6();
int uv_af_unix();
int uv_af_unspec();

// ai_socktype constants
int uv_sock_stream();
int uv_sock_dgram();
int uv_sock_raw();
int uv_sock_any();
int uv_ipproto_ip();
int uv_ipproto_ipv6();
int uv_ipproto_icmp();
int uv_ipproto_raw();
int uv_ipproto_tcp();
int uv_ipproto_udp();

// Run modes
int uv_run_default();
int uv_run_once();
int uv_run_nowait();

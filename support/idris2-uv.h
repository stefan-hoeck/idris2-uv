uv_buf_t uv_deref_buf(uv_buf_t* ptr);

char* uv_get_buf_base(uv_buf_t* buf);

unsigned int* uv_get_buf_len(uv_buf_t* buf);

void* uv_set_buf_base(uv_buf_t* buf, char * dat);

void* uv_set_buf_len(uv_buf_t* buf, unsigned int length);

void* uv_copy_buf(char * src, char * dest, int len);

void* uv_init_buf(uv_buf_t * buf, char * base, unsigned int len);

int uv_fs_close_sync(uv_loop_t *loop, uv_file file);

int uv_fs_write_sync(uv_loop_t *loop, uv_file file, const uv_buf_t bufs[], unsigned int nbufs, int64_t offset);

int uv_EOF();

// `addrinfo` setters and getters
void* uv_set_ai_family(struct addrinfo* info, int family);

void* uv_set_ai_socktype(struct addrinfo* info, int socktype);

void* uv_set_ai_protocol(struct addrinfo* info, int protocol);

void* uv_set_ai_flags(struct addrinfo* info, int flags);

int uv_get_ai_family(struct addrinfo* info);

int uv_get_ai_socktype(struct addrinfo* info);

int uv_get_ai_protocol(struct addrinfo* info);

int uv_get_ai_flags(struct addrinfo* info);

struct sockaddr* uv_get_ai_addr(struct addrinfo* info);

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

// Size of uv_buf struct
size_t uv_buf_sz();

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

// Error codes
int uv_EOF();

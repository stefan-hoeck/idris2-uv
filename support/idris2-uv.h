char* uv_get_buf_base(uv_buf_t* buf);

unsigned int* uv_get_buf_len(uv_buf_t* buf);

void* uv_set_buf_base(uv_buf_t* buf, char* dat);

void* uv_set_buf_len(uv_buf_t* buf, unsigned int length);

void* uv_copy_buf(uv_buf_t* buf, char* dest, int len);

void* uv_init_buf(uv_buf_t* buf, char *base, unsigned int len);

int uv_fs_close_sync(uv_loop_t *loop, uv_file file);

size_t uv_sockaddr_in_size();

size_t uv_sockaddr_in6_size();

size_t uv_sockaddr_size();

int uv_EOF();

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

int uv_rdonly();
int uv_wronly();
int uv_rdwr();
int uv_append();
int uv_creat();

int uv_S_IRWXU();
int uv_S_IRUSR();
int uv_S_IWUSR();
int uv_S_IXUSR();
int uv_S_IRWXG();
int uv_S_IRGRP();
int uv_S_IWGRP();
int uv_S_IXGRP();
int uv_S_IRWXO();
int uv_S_IROTH();
int uv_S_IWOTH();
int uv_S_IXOTH();

int uv_ASYNC();
int uv_CHECK();
int uv_FS_EVENT();
int uv_FS_POLL();
int uv_HANDLE();
int uv_IDLE();
int uv_NAMED_PIPE();
int uv_POLL();
int uv_PREPARE();
int uv_PROCESS();
int uv_STREAM();
int uv_TCP();
int uv_TIMER();
int uv_TTY();
int uv_UDP();
int uv_SIGNAL();

int uv_REQ();
int uv_CONNECT();
int uv_WRITE();
int uv_SHUTDOWN();
int uv_UDP_SEND();
int uv_FS();
int uv_WORK();
int uv_GETADDRINFO();
int uv_GETNAMEINFO();

int uv_buf_size();

int uv_EOF();

// Timers
uv_timer_t* uv_init_timer(uv_loop_t* loop);

// Signals
uv_signal_t* uv_init_signal(uv_loop_t* loop);

// Files
uv_fs_t* uv_alloc_fs()

uv_buf_t* uv_init_buf(unsigned int length)

void* uv_free_buf(uv_buf_t* buf)

int uv_read_fs(uv_loop_t* loop, uv_fs_t* req, uv_file file, uv_buf_t* buf, int64_t offset, uv_fs_cb cb)

int uv_fs_result(uv_fs_t* fs)

void* uv_copy_buf(uv_buf_t* buf, char* dest);

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

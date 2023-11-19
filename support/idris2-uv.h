uv_timer_t* uv_init_timer(uv_loop_t* loop);

void* uv_free_timer(uv_timer_t* timer);

uv_signal_t* uv_init_signal(uv_loop_t* loop);

void* uv_free_signal(uv_signal_t* signal);

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

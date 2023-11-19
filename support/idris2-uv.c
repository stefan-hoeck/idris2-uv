#include <stdlib.h>
#include <stdio.h>
#include <uv.h>

uv_timer_t* uv_init_timer(uv_loop_t* loop){
  uv_timer_t* timer = malloc(sizeof(uv_timer_t));
  uv_timer_init(loop, timer);
  return timer;
}

void* uv_free_timer(uv_timer_t* timer){
  free(timer);
}

uv_signal_t* uv_init_signal(uv_loop_t* loop){
  uv_signal_t* signal = malloc(sizeof(uv_signal_t));
  uv_signal_init(loop, signal);
  return signal;
}

void* uv_free_signal(uv_signal_t* signal){
  free(signal);
}

int uv_sigabrt() {return SIGABRT;}
int uv_sigfpe() {return SIGFPE;}
int uv_sighup() {return SIGHUP;}
int uv_sigill() {return SIGILL;}
int uv_sigint() {return SIGINT;}
int uv_sigquit() {return SIGQUIT;}
int uv_sigsegv() {return SIGSEGV;}
int uv_sigtrap() {return SIGTRAP;}
int uv_sigusr1() {return SIGUSR1;}
int uv_sigusr2() {return SIGUSR2;}

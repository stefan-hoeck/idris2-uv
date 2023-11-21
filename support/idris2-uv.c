#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <uv.h>

// Allocate memory for a timer and initialize it at the
// event loop
uv_timer_t* uv_init_timer(uv_loop_t* loop){
  uv_timer_t* timer = malloc(sizeof(uv_timer_t));
  uv_timer_init(loop, timer);
  return timer;
}

// Allocate memory for a signal handler and initialize it at the
// event loop
uv_signal_t* uv_init_signal(uv_loop_t* loop){
  uv_signal_t* signal = malloc(sizeof(uv_signal_t));
  uv_signal_init(loop, signal);
  return signal;
}

// Allocate memory for a file handle
uv_fs_t* uv_alloc_fs(){
  uv_fs_t* fs = malloc(sizeof(uv_fs_t));
  return fs;
}

// Extract the result int from an `uv_fs_t`.
int uv_fs_result(uv_fs_t* fs){
  return fs->result;
}

// Allocate memore for reading a char array of the given
// length and initialize an `uv_buf_t` with this.
uv_buf_t* uv_init_buf(unsigned int length){
  char *dat = NULL;
  dat = malloc(length * sizeof *dat);
  uv_buf_t* buf = malloc(sizeof(uv_buf_t));
  *buf = uv_buf_init(dat,length);
  return buf;
}

void* uv_free_buf(uv_buf_t* buf){
  free(buf->base);
  free(buf);
}

void* uv_copy_buf(uv_buf_t* buf, char* dest){
  memcpy(dest, buf->base, buf->len);
}

// Read data from a file
int uv_read_fs(uv_loop_t *loop, uv_fs_t *req, uv_file file, uv_buf_t* buf, int64_t offset, uv_fs_cb cb){
  return uv_fs_read(loop, req, file, buf, 1, offset, cb);
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

int uv_rdonly() {return O_RDONLY;}
int uv_wronly() {return O_WRONLY;}
int uv_rdwr()   {return O_RDWR;}
int uv_append() {return O_APPEND;}
int uv_creat()  {return O_CREAT;}

int uv_S_IRWXU() {return S_IRWXU;}
int uv_S_IRUSR() {return S_IRUSR;}
int uv_S_IWUSR() {return S_IWUSR;}
int uv_S_IXUSR() {return S_IXUSR;}
int uv_S_IRWXG() {return S_IRWXG;}
int uv_S_IRGRP() {return S_IRGRP;}
int uv_S_IWGRP() {return S_IWGRP;}
int uv_S_IXGRP() {return S_IXGRP;}
int uv_S_IRWXO() {return S_IRWXO;}
int uv_S_IROTH() {return S_IROTH;}
int uv_S_IWOTH() {return S_IWOTH;}
int uv_S_IXOTH() {return S_IXOTH;}

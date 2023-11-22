#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <uv.h>

// Allocate memore for reading a char array of the given
// length and initialize an `uv_buf_t` with this.
uv_buf_t* uv_init_buf(unsigned int length){
  char *dat = NULL;
  dat = malloc(length);
  uv_buf_t* buf = malloc(sizeof(uv_buf_t));
  *buf = uv_buf_init(dat,length);
  return buf;
}

void* uv_free_buf(uv_buf_t* buf){
  free(buf->base);
  free(buf);
}

void* uv_set_buf_len(uv_buf_t* buf, unsigned int length){
  buf->len = length;
}

void* uv_copy_buf(uv_buf_t* buf, char* dest, int len){
  memcpy(dest, buf->base, len);
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

int uv_UNKNOWN_HANDLE() {return UV_UNKNOWN_HANDLE;}
int uv_ASYNC() {return UV_ASYNC;}
int uv_CHECK() {return UV_CHECK;}
int uv_FS_EVENT() {return UV_FS_EVENT;}
int uv_FS_POLL() {return UV_FS_POLL;}
int uv_HANDLE() {return UV_HANDLE;}
int uv_IDLE() {return UV_IDLE;}
int uv_NAMED_PIPE() {return UV_NAMED_PIPE;}
int uv_POLL() {return UV_POLL;}
int uv_PREPARE() {return UV_PREPARE;}
int uv_PROCESS() {return UV_PROCESS;}
int uv_STREAM() {return UV_STREAM;}
int uv_TCP() {return UV_TCP;}
int uv_TIMER() {return UV_TIMER;}
int uv_TTY() {return UV_TTY;}
int uv_UDP() {return UV_UDP;}
int uv_SIGNAL() {return UV_SIGNAL;}
int uv_FILE() {return UV_FILE;}

int uv_UNKNOWN_REQ() {return UV_UNKNOWN_REQ;}
int uv_REQ() {return UV_REQ;}
int uv_CONNECT() {return UV_CONNECT;}
int uv_WRITE() {return UV_WRITE;}
int uv_SHUTDOWN() {return UV_SHUTDOWN;}
int uv_UDP_SEND() {return UV_UDP_SEND;}
int uv_FS() {return UV_FS;}
int uv_WORK() {return UV_WORK;}
int uv_GETADDRINFO() {return UV_GETADDRINFO;}
int uv_GETNAMEINFO() {return UV_GETNAMEINFO;}
int uv_REQ_TYPE_MAX() {return UV_REQ_TYPE_MAX;}

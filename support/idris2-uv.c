#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <uv.h>

uv_buf_t uv_deref_buf(uv_buf_t* ptr) {return *ptr;}

void* uv_set_buf_len(uv_buf_t* buf, unsigned int length){
  buf->len = length;
}

unsigned int uv_get_buf_len(uv_buf_t* buf) {return buf->len;}

char* uv_get_buf_base(uv_buf_t* buf) {return buf->base;}

void* uv_set_buf_base(uv_buf_t* buf, char* dat){
  buf->base = dat;
}

void* uv_copy_buf(char * src, char * dest, int len){
  memcpy(dest, src, len);
}

int uv_fs_close_sync(uv_loop_t *loop, uv_file file) {
  uv_fs_t req;
  return uv_fs_close(loop, &req, file, NULL);
}

int uv_fs_write_sync(uv_loop_t *loop, uv_file file, const uv_buf_t bufs[], unsigned int nbufs, int64_t offset) {
  uv_fs_t req;
  int res = uv_fs_write(loop, &req, file, bufs, nbufs, offset, NULL);
  uv_fs_req_cleanup(&req);
  return res;
}

void* uv_init_buf(uv_buf_t * buf, char * base, unsigned int len){
  *buf = uv_buf_init(base, len);
  return buf;
}

// `addrinfo` setters and getters
void* uv_set_ai_family(struct addrinfo* info, int family){info->ai_family = family;}

void* uv_set_ai_socktype(struct addrinfo* info, int socktype){info->ai_socktype = socktype;}

void* uv_set_ai_protocol(struct addrinfo* info, int protocol){info->ai_protocol = protocol;}

void* uv_set_ai_flags(struct addrinfo* info, int flags){info->ai_flags = flags;}

int uv_get_ai_family(struct addrinfo* info){return info->ai_family;}

int uv_get_ai_socktype(struct addrinfo* info){return info->ai_socktype;}

int uv_get_ai_protocol(struct addrinfo* info){return info->ai_protocol;}

int uv_get_ai_flags(struct addrinfo* info){return info->ai_flags;}

struct sockaddr* uv_get_ai_addr(struct addrinfo* info){return info->ai_addr;}

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

int uv_s_irwxu() {return S_IRWXU;}
int uv_s_irusr() {return S_IRUSR;}
int uv_s_iwusr() {return S_IWUSR;}
int uv_s_ixusr() {return S_IXUSR;}
int uv_s_irwxg() {return S_IRWXG;}
int uv_s_irgrp() {return S_IRGRP;}
int uv_s_iwgrp() {return S_IWGRP;}
int uv_s_ixgrp() {return S_IXGRP;}
int uv_s_irwxo() {return S_IRWXO;}
int uv_s_iroth() {return S_IROTH;}
int uv_s_iwoth() {return S_IWOTH;}
int uv_s_ixoth() {return S_IXOTH;}

size_t uv_async_sz() {return uv_handle_size(UV_ASYNC);}
size_t uv_check_sz() {return uv_handle_size(UV_CHECK);}
size_t uv_fs_event_sz() {return uv_handle_size(UV_FS_EVENT);}
size_t uv_fs_poll_sz() {return uv_handle_size(UV_FS_POLL);}
size_t uv_handle_sz() {return uv_handle_size(UV_HANDLE);}
size_t uv_idle_sz() {return uv_handle_size(UV_IDLE);}
size_t uv_named_pipe_sz() {return uv_handle_size(UV_NAMED_PIPE);}
size_t uv_poll_sz() {return uv_handle_size(UV_POLL);}
size_t uv_prepare_sz() {return uv_handle_size(UV_PREPARE);}
size_t uv_process_sz() {return uv_handle_size(UV_PROCESS);}
size_t uv_stream_sz() {return uv_handle_size(UV_STREAM);}
size_t uv_tcp_sz() {return uv_handle_size(UV_TCP);}
size_t uv_timer_sz() {return uv_handle_size(UV_TIMER);}
size_t uv_tty_sz() {return uv_handle_size(UV_TTY);}
size_t uv_udp_sz() {return uv_handle_size(UV_UDP);}
size_t uv_signal_sz() {return uv_handle_size(UV_SIGNAL);}

size_t uv_req_sz() {return uv_req_size(UV_REQ);}
size_t uv_connect_sz() {return uv_req_size(UV_CONNECT);}
size_t uv_write_sz() {return uv_req_size(UV_WRITE);}
size_t uv_shutdown_sz() {return uv_req_size(UV_SHUTDOWN);}
size_t uv_udp_send_sz() {return uv_req_size(UV_UDP_SEND);}
size_t uv_fs_sz() {return uv_req_size(UV_FS);}
size_t uv_work_sz() {return uv_req_size(UV_WORK);}
size_t uv_getaddrinfo_sz() {return uv_req_size(UV_GETADDRINFO);}
size_t uv_getnameinfo_sz() {return uv_req_size(UV_GETNAMEINFO);}

size_t uv_buf_sz() {return sizeof(uv_buf_t);}
size_t uv_loop_sz() {return sizeof(uv_loop_t);}
size_t uv_sockaddr_in_sz() {return sizeof(struct sockaddr_in);}
size_t uv_sockaddr_in6_sz() {return sizeof(struct sockaddr_in6);}
size_t uv_sockaddr_sz() {return sizeof(struct sockaddr);}
size_t uv_addrinfo_sz() {return sizeof(struct addrinfo);}

int uv_af_inet() {return AF_INET;}
int uv_af_inet6() {return AF_INET6;}
int uv_af_unix() {return AF_UNIX;}
int uv_af_unspec() {return AF_UNSPEC;}
int uv_sock_stream() {return SOCK_STREAM;}
int uv_sock_dgram() {return SOCK_DGRAM;}
int uv_sock_raw() {return SOCK_RAW;}
int uv_sock_any() {return 0;}
int uv_ipproto_ip() { return IPPROTO_IP; }
int uv_ipproto_ipv6() { return IPPROTO_IPV6; }
int uv_ipproto_icmp() { return IPPROTO_ICMP; }
int uv_ipproto_raw() { return IPPROTO_RAW; }
int uv_ipproto_tcp() { return IPPROTO_TCP; }
int uv_ipproto_udp() { return IPPROTO_UDP; }

int uv_run_default() {return UV_RUN_DEFAULT;}
int uv_run_once() {return UV_RUN_ONCE;}
int uv_run_nowait() {return UV_RUN_NOWAIT;}

int uv_EOF() {return UV_EOF;}

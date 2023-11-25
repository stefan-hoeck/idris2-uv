#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <uv.h>

void* uv_set_buf_len(uv_buf_t* buf, unsigned int length){
  buf->len = length;
}

unsigned int uv_get_buf_len(uv_buf_t* buf) {return buf->len;}

char* uv_get_buf_base(uv_buf_t* buf) {return buf->base;}

void* uv_set_buf_base(uv_buf_t* buf, char* dat){
  buf->base = dat;
}

void* uv_copy_buf(uv_buf_t* buf, char* dest, int len){
  memcpy(dest, buf->base, len);
}

int uv_fs_close_sync(uv_loop_t *loop, uv_file file) {
  uv_fs_t req;
  return uv_fs_close(loop, &req, file, NULL);
}

void* uv_init_buf(uv_buf_t* buf, char *base, unsigned int len){
  *buf = uv_buf_init(base, len);
}

size_t uv_sockaddr_in_size() {return sizeof(struct sockaddr_in);}

size_t uv_sockaddr_in6_size() {return sizeof(struct sockaddr_in6);}

size_t uv_sockaddr_size() {return sizeof(struct sockaddr);}

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

int uv_ASYNC() {return uv_handle_size(UV_ASYNC);}
int uv_CHECK() {return uv_handle_size(UV_CHECK);}
int uv_FS_EVENT() {return uv_handle_size(UV_FS_EVENT);}
int uv_FS_POLL() {return uv_handle_size(UV_FS_POLL);}
int uv_HANDLE() {return uv_handle_size(UV_HANDLE);}
int uv_IDLE() {return uv_handle_size(UV_IDLE);}
int uv_NAMED_PIPE() {return uv_handle_size(UV_NAMED_PIPE);}
int uv_POLL() {return uv_handle_size(UV_POLL);}
int uv_PREPARE() {return uv_handle_size(UV_PREPARE);}
int uv_PROCESS() {return uv_handle_size(UV_PROCESS);}
int uv_STREAM() {return uv_handle_size(UV_STREAM);}
int uv_TCP() {return uv_handle_size(UV_TCP);}
int uv_TIMER() {return uv_handle_size(UV_TIMER);}
int uv_TTY() {return uv_handle_size(UV_TTY);}
int uv_UDP() {return uv_handle_size(UV_UDP);}
int uv_SIGNAL() {return uv_handle_size(UV_SIGNAL);}

int uv_REQ() {return uv_req_size(UV_REQ);}
int uv_CONNECT() {return uv_req_size(UV_CONNECT);}
int uv_WRITE() {return uv_req_size(UV_WRITE);}
int uv_SHUTDOWN() {return uv_req_size(UV_SHUTDOWN);}
int uv_UDP_SEND() {return uv_req_size(UV_UDP_SEND);}
int uv_FS() {return uv_req_size(UV_FS);}
int uv_WORK() {return uv_req_size(UV_WORK);}
int uv_GETADDRINFO() {return uv_req_size(UV_GETADDRINFO);}
int uv_GETNAMEINFO() {return uv_req_size(UV_GETNAMEINFO);}

int uv_buf_size() {return sizeof(uv_buf_t);}

int uv_addrinfo_size() {return sizeof(struct addrinfo);}
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

int uv_EOF() {return UV_EOF;}

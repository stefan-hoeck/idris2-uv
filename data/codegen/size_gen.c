#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <uv.h>

int main(void) {
  #define XX(code, tpe) printf("\npublic export %%inline\nSZ_" #code " : Bits32\nSZ_" #code " = %zd\n", uv_handle_size(UV_ ## code));
  UV_HANDLE_TYPE_MAP(XX)
  #undef XX
  #define XX(code, tpe) printf("\npublic export %%inline\nSZ_" #code " : Bits32\nSZ_" #code " = %zd\n", uv_req_size(UV_ ## code));
  UV_REQ_TYPE_MAP(XX)
  #undef XX

  printf("\npublic export %%inline\n");
  printf("SZ_BUF : Bits32\n");
  printf("SZ_BUF = %zd\n", sizeof(uv_buf_t));

  printf("\npublic export %%inline\n");
  printf("SZ_LOOP : Bits32\n");
  printf("SZ_LOOP = %zd\n", sizeof(uv_loop_t));

  printf("\npublic export %%inline\n");
  printf("SZ_SOCKADDR_IN : Bits32\n");
  printf("SZ_SOCKADDR_IN = %zd\n", sizeof(struct sockaddr_in));

  printf("\npublic export %%inline\n");
  printf("SZ_SOCKADDR_IN6 : Bits32\n");
  printf("SZ_SOCKADDR_IN6 = %zd\n", sizeof(struct sockaddr_in6));

  printf("\npublic export %%inline\n");
  printf("SZ_SOCKADDR : Bits32\n");
  printf("SZ_SOCKADDR = %zd\n", sizeof(struct sockaddr));

  printf("\npublic export %%inline\n");
  printf("SZ_ADDRINFO : Bits32\n");
  printf("SZ_ADDRINFO = %zd\n", sizeof(struct addrinfo));
}


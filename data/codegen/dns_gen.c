// Copyright Stefan Höck

#include <stdio.h>
#include <uv.h>

int main(void) {

  printf("\npublic export\nfamilyCode : SockFamily -> Bits32\n");
  printf("familyCode AF_INET   = %d\n", AF_INET);
  printf("familyCode AF_INET6  = %d\n", AF_INET6);
  printf("familyCode AF_UNIX   = %d\n", AF_UNIX);
  printf("familyCode AF_UNSPEC = %d\n", AF_UNSPEC);

  printf("\npublic export\nsockCode : SockType -> Bits32\n");
  printf("sockCode Stream = %d\n", SOCK_STREAM);
  printf("sockCode Datagram = %d\n", SOCK_DGRAM);
  printf("sockCode Raw = %d\n", SOCK_RAW);
  printf("sockCode Any = %d\n", 0);

  printf("\npublic export\nprotocolCode : Protocol -> Bits32\n");
  printf("protocolCode IPPROTO_IP   = %d\n", IPPROTO_IP);
  printf("protocolCode IPPROTO_IPV6 = %d\n", IPPROTO_IPV6);
  printf("protocolCode IPPROTO_ICMP = %d\n", IPPROTO_ICMP);
  printf("protocolCode IPPROTO_RAW  = %d\n", IPPROTO_RAW);
  printf("protocolCode IPPROTO_TCP  = %d\n", IPPROTO_TCP);
  printf("protocolCode IPPROTO_UDP  = %d\n", IPPROTO_UDP);
}

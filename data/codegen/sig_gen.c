// Copyright Stefan Höck

#include <stdio.h>
#include <uv.h>


int main(void) {
  printf("\npublic export\n");
  printf("sigToCode : SigCode -> Bits32\n");
  printf("sigToCode SIGABRT = %d\n", SIGABRT);
  printf("sigToCode SIGFPE  = %d\n", SIGFPE);
  printf("sigToCode SIGHUP  = %d\n", SIGHUP);
  printf("sigToCode SIGILL  = %d\n", SIGILL);
  printf("sigToCode SIGINT  = %d\n", SIGINT);
  printf("sigToCode SIGQUIT = %d\n", SIGQUIT);
  printf("sigToCode SIGSEGV = %d\n", SIGSEGV);
  printf("sigToCode SIGTRAP = %d\n", SIGTRAP);
  printf("sigToCode SIGUSR1 = %d\n", SIGUSR1);
  printf("sigToCode SIGUSR2 = %d\n", SIGUSR2);

  printf("\npublic export\n");
  printf("sigFromCode : Bits32 -> SigCode\n");
  printf("sigFromCode %d = SIGABRT\n", SIGABRT);
  printf("sigFromCode %d = SIGFPE \n", SIGFPE);
  printf("sigFromCode %d = SIGHUP \n", SIGHUP);
  printf("sigFromCode %d = SIGILL \n", SIGILL);
  printf("sigFromCode %d = SIGINT \n", SIGINT);
  printf("sigFromCode %d = SIGQUIT\n", SIGQUIT);
  printf("sigFromCode %d = SIGSEGV\n", SIGSEGV);
  printf("sigFromCode %d = SIGTRAP\n", SIGTRAP);
  printf("sigFromCode %d = SIGUSR1\n", SIGUSR1);
  printf("sigFromCode _ = SIGUSR2\n");
}

// Copyright Stefan Höck

#include <stdio.h>
#include <uv.h>

int main(void) {
  printf("module System.UV.Data.Error\n\n");

  printf("import Derive.Prelude\n\n");

  printf("%%language ElabReflection\n");
  printf("%%default total\n\n");

  printf("public export\n");
  printf("data UVError : Type where\n");
#define XX(code, _) printf("  %s : UVError\n", uv_err_name(UV_##code));
  UV_ERRNO_MAP(XX)
#undef XX

  printf("\n%%runElab derive \"UVError\" [Show,Eq]\n");

  printf("\nexport\n");
  printf("toCode : UVError -> Int32\n");
#define XX(code, _)                                                            \
  printf("toCode %s = (%d)\n", uv_err_name(UV_##code), UV_##code);
  UV_ERRNO_MAP(XX)
#undef XX

  printf("\nexport\n");
  printf("fromCode : Int32 -> UVError\n");
#define XX(code, _)                                                            \
  printf("fromCode (%d) = %s\n", UV_##code, uv_err_name(UV_##code));
  UV_ERRNO_MAP(XX)
#undef XX
  printf("fromCode _ = UNKNOWN\n");

  printf("\n%%foreign \"C:uv_strerror,libuv-idris\"\n");
  printf("uv_strerror : Int32 -> String\n");

  printf("\nexport %%inline\n");
  printf("errorMsg : UVError -> String\n");
  printf("errorMsg = uv_strerror . toCode\n");

  printf("\nexport %%inline\n");
  printf("Interpolation UVError where\n");
  printf("  interpolate err = \"\{errorMsg err} (\{show err})\"\n");
}

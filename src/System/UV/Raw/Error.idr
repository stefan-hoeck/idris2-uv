module System.UV.Raw.Error

import System.UV.Raw.Pointer
import System.UV.Raw.Util

%default total

export %foreign (idris_uv "uv_e2big")
uv_e2big : Int32

export %foreign (idris_uv "uv_eacces")
uv_eacces : Int32

export %foreign (idris_uv "uv_eaddrinuse")
uv_eaddrinuse : Int32

export %foreign (idris_uv "uv_eaddrnotavail")
uv_eaddrnotavail : Int32

export %foreign (idris_uv "uv_eafnosupport")
uv_eafnosupport : Int32

export %foreign (idris_uv "uv_eagain")
uv_eagain : Int32

export %foreign (idris_uv "uv_eai_addrfamily")
uv_eai_addrfamily : Int32

export %foreign (idris_uv "uv_eai_again")
uv_eai_again : Int32

export %foreign (idris_uv "uv_eai_badflags")
uv_eai_badflags : Int32

export %foreign (idris_uv "uv_eai_badhints")
uv_eai_badhints : Int32

export %foreign (idris_uv "uv_eai_canceled")
uv_eai_canceled : Int32

export %foreign (idris_uv "uv_eai_fail")
uv_eai_fail : Int32

export %foreign (idris_uv "uv_eai_family")
uv_eai_family : Int32

export %foreign (idris_uv "uv_eai_memory")
uv_eai_memory : Int32

export %foreign (idris_uv "uv_eai_nodata")
uv_eai_nodata : Int32

export %foreign (idris_uv "uv_eai_noname")
uv_eai_noname : Int32

export %foreign (idris_uv "uv_eai_overflow")
uv_eai_overflow : Int32

export %foreign (idris_uv "uv_eai_protocol")
uv_eai_protocol : Int32

export %foreign (idris_uv "uv_eai_service")
uv_eai_service : Int32

export %foreign (idris_uv "uv_eai_socktype")
uv_eai_socktype : Int32

export %foreign (idris_uv "uv_ealready")
uv_ealready : Int32

export %foreign (idris_uv "uv_ebadf")
uv_ebadf : Int32

export %foreign (idris_uv "uv_ebusy")
uv_ebusy : Int32

export %foreign (idris_uv "uv_ecanceled")
uv_ecanceled : Int32

export %foreign (idris_uv "uv_echarset")
uv_echarset : Int32

export %foreign (idris_uv "uv_econnaborted")
uv_econnaborted : Int32

export %foreign (idris_uv "uv_econnrefused")
uv_econnrefused : Int32

export %foreign (idris_uv "uv_econnreset")
uv_econnreset : Int32

export %foreign (idris_uv "uv_edestaddrreq")
uv_edestaddrreq : Int32

export %foreign (idris_uv "uv_eexist")
uv_eexist : Int32

export %foreign (idris_uv "uv_efault")
uv_efault : Int32

export %foreign (idris_uv "uv_efbig")
uv_efbig : Int32

export %foreign (idris_uv "uv_ehostunreach")
uv_ehostunreach : Int32

export %foreign (idris_uv "uv_eintr")
uv_eintr : Int32

export %foreign (idris_uv "uv_einval")
uv_einval : Int32

export %foreign (idris_uv "uv_eio")
uv_eio : Int32

export %foreign (idris_uv "uv_eisconn")
uv_eisconn : Int32

export %foreign (idris_uv "uv_eisdir")
uv_eisdir : Int32

export %foreign (idris_uv "uv_eloop")
uv_eloop : Int32

export %foreign (idris_uv "uv_emfile")
uv_emfile : Int32

export %foreign (idris_uv "uv_emsgsize")
uv_emsgsize : Int32

export %foreign (idris_uv "uv_enametoolong")
uv_enametoolong : Int32

export %foreign (idris_uv "uv_enetdown")
uv_enetdown : Int32

export %foreign (idris_uv "uv_enetunreach")
uv_enetunreach : Int32

export %foreign (idris_uv "uv_enfile")
uv_enfile : Int32

export %foreign (idris_uv "uv_enobufs")
uv_enobufs : Int32

export %foreign (idris_uv "uv_enodev")
uv_enodev : Int32

export %foreign (idris_uv "uv_enoent")
uv_enoent : Int32

export %foreign (idris_uv "uv_enomem")
uv_enomem : Int32

export %foreign (idris_uv "uv_enonet")
uv_enonet : Int32

export %foreign (idris_uv "uv_enoprotoopt")
uv_enoprotoopt : Int32

export %foreign (idris_uv "uv_enospc")
uv_enospc : Int32

export %foreign (idris_uv "uv_enosys")
uv_enosys : Int32

export %foreign (idris_uv "uv_enotconn")
uv_enotconn : Int32

export %foreign (idris_uv "uv_enotdir")
uv_enotdir : Int32

export %foreign (idris_uv "uv_enotempty")
uv_enotempty : Int32

export %foreign (idris_uv "uv_enotsock")
uv_enotsock : Int32

export %foreign (idris_uv "uv_enotsup")
uv_enotsup : Int32

export %foreign (idris_uv "uv_eoverflow")
uv_eoverflow : Int32

export %foreign (idris_uv "uv_eperm")
uv_eperm : Int32

export %foreign (idris_uv "uv_epipe")
uv_epipe : Int32

export %foreign (idris_uv "uv_eproto")
uv_eproto : Int32

export %foreign (idris_uv "uv_eprotonosupport")
uv_eprotonosupport : Int32

export %foreign (idris_uv "uv_eprototype")
uv_eprototype : Int32

export %foreign (idris_uv "uv_erange")
uv_erange : Int32

export %foreign (idris_uv "uv_erofs")
uv_erofs : Int32

export %foreign (idris_uv "uv_eshutdown")
uv_eshutdown : Int32

export %foreign (idris_uv "uv_espipe")
uv_espipe : Int32

export %foreign (idris_uv "uv_esrch")
uv_esrch : Int32

export %foreign (idris_uv "uv_etimedout")
uv_etimedout : Int32

export %foreign (idris_uv "uv_etxtbsy")
uv_etxtbsy : Int32

export %foreign (idris_uv "uv_exdev")
uv_exdev : Int32

export %foreign (idris_uv "uv_unknown")
uv_unknown : Int32

export %foreign (idris_uv "uv_eof")
uv_eof : Int32

export %foreign (idris_uv "uv_enxio")
uv_enxio : Int32

export %foreign (idris_uv "uv_emlink")
uv_emlink : Int32

export %foreign (idris_uv "uv_enotty")
uv_enotty : Int32

export %foreign (idris_uv "uv_eftype")
uv_eftype : Int32

export %foreign (idris_uv "uv_eilseq")
uv_eilseq : Int32

export %foreign (idris_uv "uv_esocktnosupport")
uv_esocktnosupport : Int32

%foreign (idris_uv "uv_strerror")
prim__uv_strerror : Int32 -> Ptr Char

%foreign (idris_uv "uv_err_name")
prim__uv_err_name : Int32 -> Ptr Char

export %inline
uv_err_name : Int32 -> String
uv_err_name = getString . prim__uv_err_name

export %inline
uv_strerror : Int32 -> String
uv_strerror = getString . prim__uv_strerror

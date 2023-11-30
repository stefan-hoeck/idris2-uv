module System.UV.Error

import Data.Maybe
import Data.SortedMap
import Derive.Prelude
import Derive.Finite
import System.UV.Pointer
import System.UV.Util

import public Control.Monad.Either
import public System.UV.Raw.Error

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

public export
data UVError : Type where
  UV_E2BIG           : UVError
  UV_EACCES          : UVError
  UV_EADDRINUSE      : UVError
  UV_EADDRNOTAVAIL   : UVError
  UV_EAFNOSUPPORT    : UVError
  UV_EAGAIN          : UVError
  UV_EAI_ADDRFAMILY  : UVError
  UV_EAI_AGAIN       : UVError
  UV_EAI_BADFLAGS    : UVError
  UV_EAI_BADHINTS    : UVError
  UV_EAI_CANCELED    : UVError
  UV_EAI_FAIL        : UVError
  UV_EAI_FAMILY      : UVError
  UV_EAI_MEMORY      : UVError
  UV_EAI_NODATA      : UVError
  UV_EAI_NONAME      : UVError
  UV_EAI_OVERFLOW    : UVError
  UV_EAI_PROTOCOL    : UVError
  UV_EAI_SERVICE     : UVError
  UV_EAI_SOCKTYPE    : UVError
  UV_EALREADY        : UVError
  UV_EBADF           : UVError
  UV_EBUSY           : UVError
  UV_ECANCELED       : UVError
  UV_ECHARSET        : UVError
  UV_ECONNABORTED    : UVError
  UV_ECONNREFUSED    : UVError
  UV_ECONNRESET      : UVError
  UV_EDESTADDRREQ    : UVError
  UV_EEXIST          : UVError
  UV_EFAULT          : UVError
  UV_EFBIG           : UVError
  UV_EHOSTUNREACH    : UVError
  UV_EINTR           : UVError
  UV_EINVAL          : UVError
  UV_EIO             : UVError
  UV_EISCONN         : UVError
  UV_EISDIR          : UVError
  UV_ELOOP           : UVError
  UV_EMFILE          : UVError
  UV_EMSGSIZE        : UVError
  UV_ENAMETOOLONG    : UVError
  UV_ENETDOWN        : UVError
  UV_ENETUNREACH     : UVError
  UV_ENFILE          : UVError
  UV_ENOBUFS         : UVError
  UV_ENODEV          : UVError
  UV_ENOENT          : UVError
  UV_ENOMEM          : UVError
  UV_ENONET          : UVError
  UV_ENOPROTOOPT     : UVError
  UV_ENOSPC          : UVError
  UV_ENOSYS          : UVError
  UV_ENOTCONN        : UVError
  UV_ENOTDIR         : UVError
  UV_ENOTEMPTY       : UVError
  UV_ENOTSOCK        : UVError
  UV_ENOTSUP         : UVError
  UV_EOVERFLOW       : UVError
  UV_EPERM           : UVError
  UV_EPIPE           : UVError
  UV_EPROTO          : UVError
  UV_EPROTONOSUPPORT : UVError
  UV_EPROTOTYPE      : UVError
  UV_ERANGE          : UVError
  UV_EROFS           : UVError
  UV_ESHUTDOWN       : UVError
  UV_ESPIPE          : UVError
  UV_ESRCH           : UVError
  UV_ETIMEDOUT       : UVError
  UV_ETXTBSY         : UVError
  UV_EXDEV           : UVError
  UV_UNKNOWN         : UVError
  UV_EOF             : UVError
  UV_ENXIO           : UVError
  UV_EMLINK          : UVError
  UV_ENOTTY          : UVError
  UV_EFTYPE          : UVError
  UV_EILSEQ          : UVError
  UV_ESOCKTNOSUPPORT : UVError

%runElab derive "UVError" [Show,Eq,Finite]

export
toCode : UVError -> Int32
toCode UV_E2BIG           = uv_e2big
toCode UV_EACCES          = uv_eacces
toCode UV_EADDRINUSE      = uv_eaddrinuse
toCode UV_EADDRNOTAVAIL   = uv_eaddrnotavail
toCode UV_EAFNOSUPPORT    = uv_eafnosupport
toCode UV_EAGAIN          = uv_eagain
toCode UV_EAI_ADDRFAMILY  = uv_eai_addrfamily
toCode UV_EAI_AGAIN       = uv_eai_again
toCode UV_EAI_BADFLAGS    = uv_eai_badflags
toCode UV_EAI_BADHINTS    = uv_eai_badhints
toCode UV_EAI_CANCELED    = uv_eai_canceled
toCode UV_EAI_FAIL        = uv_eai_fail
toCode UV_EAI_FAMILY      = uv_eai_family
toCode UV_EAI_MEMORY      = uv_eai_memory
toCode UV_EAI_NODATA      = uv_eai_nodata
toCode UV_EAI_NONAME      = uv_eai_noname
toCode UV_EAI_OVERFLOW    = uv_eai_overflow
toCode UV_EAI_PROTOCOL    = uv_eai_protocol
toCode UV_EAI_SERVICE     = uv_eai_service
toCode UV_EAI_SOCKTYPE    = uv_eai_socktype
toCode UV_EALREADY        = uv_ealready
toCode UV_EBADF           = uv_ebadf
toCode UV_EBUSY           = uv_ebusy
toCode UV_ECANCELED       = uv_ecanceled
toCode UV_ECHARSET        = uv_echarset
toCode UV_ECONNABORTED    = uv_econnaborted
toCode UV_ECONNREFUSED    = uv_econnrefused
toCode UV_ECONNRESET      = uv_econnreset
toCode UV_EDESTADDRREQ    = uv_edestaddrreq
toCode UV_EEXIST          = uv_eexist
toCode UV_EFAULT          = uv_efault
toCode UV_EFBIG           = uv_efbig
toCode UV_EHOSTUNREACH    = uv_ehostunreach
toCode UV_EINTR           = uv_eintr
toCode UV_EINVAL          = uv_einval
toCode UV_EIO             = uv_eio
toCode UV_EISCONN         = uv_eisconn
toCode UV_EISDIR          = uv_eisdir
toCode UV_ELOOP           = uv_eloop
toCode UV_EMFILE          = uv_emfile
toCode UV_EMSGSIZE        = uv_emsgsize
toCode UV_ENAMETOOLONG    = uv_enametoolong
toCode UV_ENETDOWN        = uv_enetdown
toCode UV_ENETUNREACH     = uv_enetunreach
toCode UV_ENFILE          = uv_enfile
toCode UV_ENOBUFS         = uv_enobufs
toCode UV_ENODEV          = uv_enodev
toCode UV_ENOENT          = uv_enoent
toCode UV_ENOMEM          = uv_enomem
toCode UV_ENONET          = uv_enonet
toCode UV_ENOPROTOOPT     = uv_enoprotoopt
toCode UV_ENOSPC          = uv_enospc
toCode UV_ENOSYS          = uv_enosys
toCode UV_ENOTCONN        = uv_enotconn
toCode UV_ENOTDIR         = uv_enotdir
toCode UV_ENOTEMPTY       = uv_enotempty
toCode UV_ENOTSOCK        = uv_enotsock
toCode UV_ENOTSUP         = uv_enotsup
toCode UV_EOVERFLOW       = uv_eoverflow
toCode UV_EPERM           = uv_eperm
toCode UV_EPIPE           = uv_epipe
toCode UV_EPROTO          = uv_eproto
toCode UV_EPROTONOSUPPORT = uv_eprotonosupport
toCode UV_EPROTOTYPE      = uv_eprototype
toCode UV_ERANGE          = uv_erange
toCode UV_EROFS           = uv_erofs
toCode UV_ESHUTDOWN       = uv_eshutdown
toCode UV_ESPIPE          = uv_espipe
toCode UV_ESRCH           = uv_esrch
toCode UV_ETIMEDOUT       = uv_etimedout
toCode UV_ETXTBSY         = uv_etxtbsy
toCode UV_EXDEV           = uv_exdev
toCode UV_UNKNOWN         = uv_unknown
toCode UV_EOF             = uv_eof
toCode UV_ENXIO           = uv_enxio
toCode UV_EMLINK          = uv_emlink
toCode UV_ENOTTY          = uv_enotty
toCode UV_EFTYPE          = uv_eftype
toCode UV_EILSEQ          = uv_eilseq
toCode UV_ESOCKTNOSUPPORT = uv_esocktnosupport

export
Interpolation UVError where
  interpolate err =
    let c := toCode err
     in "\{uv_strerror c} (\{uv_err_name c})"

public export
0 UVIO : Type -> Type
UVIO = EitherT UVError IO

codeMap : SortedMap Int32 UVError
codeMap = fromList $ map (\v => (toCode v, v)) values

export
fromCode : Int32 -> UVError
fromCode v = fromMaybe UV_UNKNOWN $ lookup v codeMap

export
uvRes : Int32 -> Either UVError ()
uvRes n = if n < 0 then Left $ fromCode n else Right ()

export %inline
toErr : Int32 -> Maybe UVError
toErr = either Just (const Nothing) . uvRes

export %inline
checkStatus : Int32 -> UVIO ()
checkStatus = MkEitherT . pure . uvRes

export %inline
uvio : IO Int32 -> UVIO ()
uvio io = MkEitherT $ uvRes <$> io

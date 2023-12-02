module System.UV.Data.Error

import Derive.Prelude

%language ElabReflection
%default total

public export
data UVError : Type where
  E2BIG : UVError
  EACCES : UVError
  EADDRINUSE : UVError
  EADDRNOTAVAIL : UVError
  EAFNOSUPPORT : UVError
  EAGAIN : UVError
  EAI_ADDRFAMILY : UVError
  EAI_AGAIN : UVError
  EAI_BADFLAGS : UVError
  EAI_BADHINTS : UVError
  EAI_CANCELED : UVError
  EAI_FAIL : UVError
  EAI_FAMILY : UVError
  EAI_MEMORY : UVError
  EAI_NODATA : UVError
  EAI_NONAME : UVError
  EAI_OVERFLOW : UVError
  EAI_PROTOCOL : UVError
  EAI_SERVICE : UVError
  EAI_SOCKTYPE : UVError
  EALREADY : UVError
  EBADF : UVError
  EBUSY : UVError
  ECANCELED : UVError
  ECHARSET : UVError
  ECONNABORTED : UVError
  ECONNREFUSED : UVError
  ECONNRESET : UVError
  EDESTADDRREQ : UVError
  EEXIST : UVError
  EFAULT : UVError
  EFBIG : UVError
  EHOSTUNREACH : UVError
  EINTR : UVError
  EINVAL : UVError
  EIO : UVError
  EISCONN : UVError
  EISDIR : UVError
  ELOOP : UVError
  EMFILE : UVError
  EMSGSIZE : UVError
  ENAMETOOLONG : UVError
  ENETDOWN : UVError
  ENETUNREACH : UVError
  ENFILE : UVError
  ENOBUFS : UVError
  ENODEV : UVError
  ENOENT : UVError
  ENOMEM : UVError
  ENONET : UVError
  ENOPROTOOPT : UVError
  ENOSPC : UVError
  ENOSYS : UVError
  ENOTCONN : UVError
  ENOTDIR : UVError
  ENOTEMPTY : UVError
  ENOTSOCK : UVError
  ENOTSUP : UVError
  EOVERFLOW : UVError
  EPERM : UVError
  EPIPE : UVError
  EPROTO : UVError
  EPROTONOSUPPORT : UVError
  EPROTOTYPE : UVError
  ERANGE : UVError
  EROFS : UVError
  ESHUTDOWN : UVError
  ESPIPE : UVError
  ESRCH : UVError
  ETIMEDOUT : UVError
  ETXTBSY : UVError
  EXDEV : UVError
  UNKNOWN : UVError
  EOF : UVError
  ENXIO : UVError
  EMLINK : UVError
  EHOSTDOWN : UVError
  EREMOTEIO : UVError
  ENOTTY : UVError
  EFTYPE : UVError
  EILSEQ : UVError
  ESOCKTNOSUPPORT : UVError
  ENODATA : UVError
  EUNATCH : UVError

%runElab derive "UVError" [Show,Eq]

export
toCode : UVError -> Int32
toCode E2BIG = (-7)
toCode EACCES = (-13)
toCode EADDRINUSE = (-98)
toCode EADDRNOTAVAIL = (-99)
toCode EAFNOSUPPORT = (-97)
toCode EAGAIN = (-11)
toCode EAI_ADDRFAMILY = (-3000)
toCode EAI_AGAIN = (-3001)
toCode EAI_BADFLAGS = (-3002)
toCode EAI_BADHINTS = (-3013)
toCode EAI_CANCELED = (-3003)
toCode EAI_FAIL = (-3004)
toCode EAI_FAMILY = (-3005)
toCode EAI_MEMORY = (-3006)
toCode EAI_NODATA = (-3007)
toCode EAI_NONAME = (-3008)
toCode EAI_OVERFLOW = (-3009)
toCode EAI_PROTOCOL = (-3014)
toCode EAI_SERVICE = (-3010)
toCode EAI_SOCKTYPE = (-3011)
toCode EALREADY = (-114)
toCode EBADF = (-9)
toCode EBUSY = (-16)
toCode ECANCELED = (-125)
toCode ECHARSET = (-4080)
toCode ECONNABORTED = (-103)
toCode ECONNREFUSED = (-111)
toCode ECONNRESET = (-104)
toCode EDESTADDRREQ = (-89)
toCode EEXIST = (-17)
toCode EFAULT = (-14)
toCode EFBIG = (-27)
toCode EHOSTUNREACH = (-113)
toCode EINTR = (-4)
toCode EINVAL = (-22)
toCode EIO = (-5)
toCode EISCONN = (-106)
toCode EISDIR = (-21)
toCode ELOOP = (-40)
toCode EMFILE = (-24)
toCode EMSGSIZE = (-90)
toCode ENAMETOOLONG = (-36)
toCode ENETDOWN = (-100)
toCode ENETUNREACH = (-101)
toCode ENFILE = (-23)
toCode ENOBUFS = (-105)
toCode ENODEV = (-19)
toCode ENOENT = (-2)
toCode ENOMEM = (-12)
toCode ENONET = (-64)
toCode ENOPROTOOPT = (-92)
toCode ENOSPC = (-28)
toCode ENOSYS = (-38)
toCode ENOTCONN = (-107)
toCode ENOTDIR = (-20)
toCode ENOTEMPTY = (-39)
toCode ENOTSOCK = (-88)
toCode ENOTSUP = (-95)
toCode EOVERFLOW = (-75)
toCode EPERM = (-1)
toCode EPIPE = (-32)
toCode EPROTO = (-71)
toCode EPROTONOSUPPORT = (-93)
toCode EPROTOTYPE = (-91)
toCode ERANGE = (-34)
toCode EROFS = (-30)
toCode ESHUTDOWN = (-108)
toCode ESPIPE = (-29)
toCode ESRCH = (-3)
toCode ETIMEDOUT = (-110)
toCode ETXTBSY = (-26)
toCode EXDEV = (-18)
toCode UNKNOWN = (-4094)
toCode EOF = (-4095)
toCode ENXIO = (-6)
toCode EMLINK = (-31)
toCode EHOSTDOWN = (-112)
toCode EREMOTEIO = (-121)
toCode ENOTTY = (-25)
toCode EFTYPE = (-4028)
toCode EILSEQ = (-84)
toCode ESOCKTNOSUPPORT = (-94)
toCode ENODATA = (-61)
toCode EUNATCH = (-49)

export
fromCode : Int32 -> UVError
fromCode (-7) = E2BIG
fromCode (-13) = EACCES
fromCode (-98) = EADDRINUSE
fromCode (-99) = EADDRNOTAVAIL
fromCode (-97) = EAFNOSUPPORT
fromCode (-11) = EAGAIN
fromCode (-3000) = EAI_ADDRFAMILY
fromCode (-3001) = EAI_AGAIN
fromCode (-3002) = EAI_BADFLAGS
fromCode (-3013) = EAI_BADHINTS
fromCode (-3003) = EAI_CANCELED
fromCode (-3004) = EAI_FAIL
fromCode (-3005) = EAI_FAMILY
fromCode (-3006) = EAI_MEMORY
fromCode (-3007) = EAI_NODATA
fromCode (-3008) = EAI_NONAME
fromCode (-3009) = EAI_OVERFLOW
fromCode (-3014) = EAI_PROTOCOL
fromCode (-3010) = EAI_SERVICE
fromCode (-3011) = EAI_SOCKTYPE
fromCode (-114) = EALREADY
fromCode (-9) = EBADF
fromCode (-16) = EBUSY
fromCode (-125) = ECANCELED
fromCode (-4080) = ECHARSET
fromCode (-103) = ECONNABORTED
fromCode (-111) = ECONNREFUSED
fromCode (-104) = ECONNRESET
fromCode (-89) = EDESTADDRREQ
fromCode (-17) = EEXIST
fromCode (-14) = EFAULT
fromCode (-27) = EFBIG
fromCode (-113) = EHOSTUNREACH
fromCode (-4) = EINTR
fromCode (-22) = EINVAL
fromCode (-5) = EIO
fromCode (-106) = EISCONN
fromCode (-21) = EISDIR
fromCode (-40) = ELOOP
fromCode (-24) = EMFILE
fromCode (-90) = EMSGSIZE
fromCode (-36) = ENAMETOOLONG
fromCode (-100) = ENETDOWN
fromCode (-101) = ENETUNREACH
fromCode (-23) = ENFILE
fromCode (-105) = ENOBUFS
fromCode (-19) = ENODEV
fromCode (-2) = ENOENT
fromCode (-12) = ENOMEM
fromCode (-64) = ENONET
fromCode (-92) = ENOPROTOOPT
fromCode (-28) = ENOSPC
fromCode (-38) = ENOSYS
fromCode (-107) = ENOTCONN
fromCode (-20) = ENOTDIR
fromCode (-39) = ENOTEMPTY
fromCode (-88) = ENOTSOCK
fromCode (-95) = ENOTSUP
fromCode (-75) = EOVERFLOW
fromCode (-1) = EPERM
fromCode (-32) = EPIPE
fromCode (-71) = EPROTO
fromCode (-93) = EPROTONOSUPPORT
fromCode (-91) = EPROTOTYPE
fromCode (-34) = ERANGE
fromCode (-30) = EROFS
fromCode (-108) = ESHUTDOWN
fromCode (-29) = ESPIPE
fromCode (-3) = ESRCH
fromCode (-110) = ETIMEDOUT
fromCode (-26) = ETXTBSY
fromCode (-18) = EXDEV
fromCode (-4094) = UNKNOWN
fromCode (-4095) = EOF
fromCode (-6) = ENXIO
fromCode (-31) = EMLINK
fromCode (-112) = EHOSTDOWN
fromCode (-121) = EREMOTEIO
fromCode (-25) = ENOTTY
fromCode (-4028) = EFTYPE
fromCode (-84) = EILSEQ
fromCode (-94) = ESOCKTNOSUPPORT
fromCode (-61) = ENODATA
fromCode (-49) = EUNATCH
fromCode _ = UNKNOWN

%foreign "C:uv_strerror,libuv-idris"
uv_strerror : Int32 -> String

export %inline
errorMsg : UVError -> String
errorMsg = uv_strerror . toCode

export %inline
Interpolation UVError where
  interpolate err = "{errorMsg err} ({show err})"

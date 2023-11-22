module System.UV.Req

import System.FFI
import System.UV.Handle
import System.UV.Loop
import System.UV.Util

%default total

export
data UnknownReq : Type where

export
data Req : Type where

export
data Connect : Type where

export
data Write : Type where

export
data Shutdown : Type where

export
data UpdSend : Type where

export
data Fs : Type where

export
data Work : Type where

export
data GetAddrInfo : Type where

export
data GetNameInfo : Type where

export
data ReqTypeMax : Type where

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_req_size")
prim__uv_req_size : Int -> Int

%foreign (idris_uv "uv_UNKNOWN_REQ")
UV_UNKNOWN_REQ : Int

%foreign (idris_uv "uv_REQ")
UV_REQ : Int

%foreign (idris_uv "uv_CONNECT")
UV_CONNECT : Int

%foreign (idris_uv "uv_WRITE")
UV_WRITE : Int

%foreign (idris_uv "uv_SHUTDOWN")
UV_SHUTDOWN : Int

%foreign (idris_uv "uv_UDP_SEND")
UV_UDP_SEND : Int

%foreign (idris_uv "uv_FS")
UV_FS : Int

%foreign (idris_uv "uv_WORK")
UV_WORK : Int

%foreign (idris_uv "uv_GETADDRINFO")
UV_GETADDRINFO : Int

%foreign (idris_uv "uv_GETNAMEINFO")
UV_GETNAMEINFO : Int

%foreign (idris_uv "uv_REQ_TYPE_MAX")
UV_REQ_TYPE_MAX : Int

--------------------------------------------------------------------------------
-- Req
--------------------------------------------------------------------------------

||| libuv req type used for allocating the required amount of memory
||| for a new req.
|||
||| Some reqs are subtyes of other reqs: Their structure is laid out
||| in such a way that they can be used where other the other type is expected.
|||
||| For instance, every libuv req can be used where a `uv_req_t`
||| (represented as `Ptr Req` in Idris) is expected.
public export
data ReqType : Type -> Type where
  UNKNOWN_REQ     : ReqType UnknownReq
  REQ             : ReqType Req
  CONNECT         : ReqType Connect
  WRITE           : ReqType Write
  SHUTDOWN        : ReqType Shutdown
  UDP_SEND        : ReqType UpdSend
  FS              : ReqType Fs
  WORK            : ReqType Work
  GETADDRINFO     : ReqType GetAddrInfo
  GETNAMEINFO     : ReqType GetNameInfo
  REQ_TYPE_MAX    : ReqType ReqTypeMax

value : ReqType t -> Int
value UNKNOWN_REQ  = UV_UNKNOWN_REQ
value REQ          = UV_REQ
value CONNECT      = UV_CONNECT
value WRITE        = UV_WRITE
value SHUTDOWN     = UV_SHUTDOWN
value UDP_SEND     = UV_UDP_SEND
value FS           = UV_FS
value WORK         = UV_WORK
value GETADDRINFO  = UV_GETADDRINFO
value GETNAMEINFO  = UV_GETNAMEINFO
value REQ_TYPE_MAX = UV_REQ_TYPE_MAX

||| Number of bytes allocated by the given req type
export %inline
reqSize : ReqType t -> Int
reqSize = prim__uv_req_size . value

||| Allocate memory for a libuv req corresponding to the given tag.
export %inline
mallocReq : HasIO io => ReqType t -> io (Ptr t)
mallocReq v = prim__castPtr <$> malloc (reqSize v)

||| Free the given libuv req.
export %inline
freeReq : HasIO io => Ptr t -> io ()
freeReq = free . prim__forgetPtr

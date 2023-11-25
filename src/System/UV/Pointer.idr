module System.UV.Pointer

import System.FFI
import System.UV.Util

%default total

--------------------------------------------------------------------------------
-- Buffers
--------------------------------------------------------------------------------

export
data Buf : Type where

export %inline
getString : Ptr String -> String
getString = prim__getString

export %inline
getStringMay : Ptr String -> Maybe String
getStringMay p =
  case prim__nullPtr p of
    0 => Just $ getString p
    _ => Nothing

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_set_buf_len")
prim__uv_set_buf_len : Ptr Buf -> Bits32 -> PrimIO ()

%foreign (idris_uv "uv_set_buf_base")
prim__uv_set_buf_base : Ptr Buf -> Ptr String -> PrimIO ()

%foreign (idris_uv "uv_get_buf_len")
prim__uv_get_buf_len : Ptr Buf -> PrimIO Bits32

%foreign (idris_uv "uv_get_buf_base")
prim__uv_get_buf_base : Ptr Buf -> PrimIO (Ptr String)

%foreign (idris_uv "uv_init_buf")
prim__uv_init_buf : Ptr Buf -> Ptr String -> Bits32 -> PrimIO ()

export %foreign (idris_uv "uv_ASYNC")
ASYNC_SIZE : Bits32

export %foreign (idris_uv "uv_CHECK")
CHECK_SIZE : Bits32

export %foreign (idris_uv "uv_FS_EVENT")
FS_EVENT_SIZE : Bits32

export %foreign (idris_uv "uv_FS_POLL")
FS_POLL_SIZE : Bits32

export %foreign (idris_uv "uv_HANDLE")
HANDLE_SIZE : Bits32

export %foreign (idris_uv "uv_IDLE")
IDLE_SIZE : Bits32

export %foreign (idris_uv "uv_NAMED_PIPE")
NAMEDPIPE_SIZE : Bits32

export %foreign (idris_uv "uv_POLL")
POLL_SIZE : Bits32

export %foreign (idris_uv "uv_PREPARE")
PREPARE_SIZE : Bits32

export %foreign (idris_uv "uv_PROCESS")
PROCESS_SIZE : Bits32

export %foreign (idris_uv "uv_STREAM")
STREAM_SIZE : Bits32

export %foreign (idris_uv "uv_TCP")
TCP_SIZE : Bits32

export %foreign (idris_uv "uv_TIMER")
TIMER_SIZE : Bits32

export %foreign (idris_uv "uv_TTY")
TTY_SIZE : Bits32

export %foreign (idris_uv "uv_UDP")
UDP_SIZE : Bits32

export %foreign (idris_uv "uv_SIGNAL")
SIGNAL_SIZE : Bits32

export %foreign (idris_uv "uv_REQ")
REQ_SIZE : Bits32

export %foreign (idris_uv "uv_CONNECT")
CONNECT_SIZE : Bits32

export %foreign (idris_uv "uv_WRITE")
WRITE_SIZE : Bits32

export %foreign (idris_uv "uv_SHUTDOWN")
SHUTDOWN_SIZE : Bits32

export %foreign (idris_uv "uv_UDP_SEND")
UDP_SEND_SIZE : Bits32

export %foreign (idris_uv "uv_FS")
FS_SIZE : Bits32

export %foreign (idris_uv "uv_WORK")
WORK_SIZE : Bits32

export %foreign (idris_uv "uv_GETADDRINFO")
GETADDRINFO_SIZE : Bits32

export %foreign (idris_uv "uv_GETNAMEINFO")
GETNAMEINFO_SIZE : Bits32

export %foreign (idris_uv "uv_sockaddr_in_size")
SOCKADDR_IN_SIZE : Bits32

export %foreign (idris_uv "uv_sockaddr_in6_size")
SOCKADDR_IN6_SIZE : Bits32

export %foreign (idris_uv "uv_sockaddr_size")
SOCKADDR_SIZE : Bits32

export %foreign (idris_uv "uv_addrinfo_size")
ADDRINFO_SIZE : Bits32

export %foreign (idris_uv "uv_buf_size")
BUF_SIZE : Bits32

--------------------------------------------------------------------------------
-- Handles
--------------------------------------------------------------------------------

export
data Async : Type where

export
data Check : Type where

export
data FsEvent : Type where

export
data FsPoll : Type where

export
data Handle : Type where

export
data Idle : Type where

export
data Pipe : Type where

export
data Poll : Type where

export
data Prepare : Type where

export
data Process : Type where

export
data Stream : Type where

export
data Tcp : Type where

export
data Timer : Type where

export
data Tty : Type where

export
data Udp : Type where

export
data Signal : Type where

--------------------------------------------------------------------------------
-- Reqs
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Sock Addresses
--------------------------------------------------------------------------------

export
data AddrInfo : Type where

export
data SockAddr : Type where

export
data SockAddrIn : Type where

export
data SockAddrIn6 : Type where

--------------------------------------------------------------------------------
-- Allocation
--------------------------------------------------------------------------------

public export
data PSize : (a : Type) -> (s : Bits32) -> Type where
  [search a]
  ASYNC          : PSize Async ASYNC_SIZE
  CHECK          : PSize Check CHECK_SIZE
  FS_EVENT       : PSize FsEvent FS_EVENT_SIZE
  FS_POLL        : PSize FsPoll FS_POLL_SIZE
  HANDLE         : PSize Handle HANDLE_SIZE
  IDLE           : PSize Idle IDLE_SIZE
  NAMEDPIPE      : PSize Pipe NAMEDPIPE_SIZE
  POLL           : PSize Poll POLL_SIZE
  PREPARE        : PSize Prepare PREPARE_SIZE
  PROCESS        : PSize Process PROCESS_SIZE
  STREAM         : PSize Stream STREAM_SIZE
  TCP            : PSize Tcp TCP_SIZE
  TIMER          : PSize Timer TIMER_SIZE
  TTY            : PSize Tty TTY_SIZE
  UDP            : PSize Udp UDP_SIZE
  SIGNAL         : PSize Signal SIGNAL_SIZE
  REQ            : PSize Req REQ_SIZE
  CONNECT        : PSize Connect CONNECT_SIZE
  WRITE          : PSize Write WRITE_SIZE
  SHUTDOWN       : PSize Shutdown SHUTDOWN_SIZE
  FS             : PSize Fs FS_SIZE
  WORK           : PSize Work WORK_SIZE
  GETADDRINFO    : PSize GetAddrInfo GETADDRINFO_SIZE
  GETNAMEINFO    : PSize GetNameInfo GETNAMEINFO_SIZE
  ADDRINFO       : PSize AddrInfo ADDRINFO_SIZE
  SOCKADDR       : PSize SockAddr SOCKADDR_SIZE
  SOCKADDRIN     : PSize SockAddrIn SOCKADDR_IN_SIZE
  SOCKADDRIN6    : PSize SockAddrIn6 SOCKADDR_IN6_SIZE
  BUF            : PSize Buf BUF_SIZE
  STRING         : PSize String 1

||| Allocates a pointer for a type of a known pointer size.
export %inline
mallocPtr :
     {auto has : HasIO io}
  -> {s : _}
  -> (0 a : Type)
  -> {auto 0 prf : PSize a s}
  -> io (Ptr a)
mallocPtr _ = prim__castPtr <$> malloc (cast s)

||| Allocates an array of pointers for a type of a known pointer size.
export %inline
mallocPtrs :
     {auto has : HasIO io}
  -> {s : _}
  -> (0 a : Type)
  -> {auto 0 prf : PSize a s}
  -> (numPtrs : Bits32)
  -> io (Ptr a)
mallocPtrs _ numPtrs = prim__castPtr <$> malloc (cast $ s * numPtrs)

||| Allocates a pointer for a type of a known pointer size.
export %inline
freePtr : HasIO io => Ptr t -> io ()
freePtr = free . prim__forgetPtr

--------------------------------------------------------------------------------
-- Safe Casts
--------------------------------------------------------------------------------

||| Pointers to some types are subtypes of pointers to other types:
||| Their structure is laid out in such a way that they can be used
||| where the other pointer type is expected.
|||
||| For instance, every libuv handle can be used where a `uv_handle_t`
||| (represented as `Ptr Handle` in Idris) is expected.
public export
data PCast : Type -> Type -> Type where
  Self                 : PCast t t
  AsyncHandle          : PCast Async Handle
  CheckHandle          : PCast Check Handle
  Fs_eventHandle       : PCast FsEvent Handle
  Fs_pollHandle        : PCast FsPoll Handle
  IdleHandle           : PCast Idle Handle
  NamedpipeHandle      : PCast Pipe Handle
  PollHandle           : PCast Poll Handle
  PrepareHandle        : PCast Prepare Handle
  ProcessHandle        : PCast Process Handle
  StreamHandle         : PCast Stream Handle
  TcpHandle            : PCast Tcp Handle
  TimerHandle          : PCast Timer Handle
  TtyHandle            : PCast Tty Handle
  UdpHandle            : PCast Udp Handle
  SignalHandle         : PCast Signal Handle
  StreamStream         : PCast Stream Stream
  TcpStream            : PCast Tcp Stream
  PipeStream           : PCast Pipe Stream
  TtyStream            : PCast Tty Stream
  IP4Addr              : PCast SockAddrIn SockAddr
  RevIP4Addr           : PCast SockAddr SockAddrIn
  IP6Addr              : PCast SockAddrIn6 SockAddr

export
castPtr : (0 _ : PCast s t) => Ptr s -> Ptr t
castPtr = believe_me

--------------------------------------------------------------------------------
-- Buffers
--------------------------------------------------------------------------------

export %inline
setBufLen : HasIO io => Ptr Buf -> Bits32 -> io ()
setBufLen p s = primIO $ prim__uv_set_buf_len p s

export %inline
setBufBase : HasIO io => Ptr Buf -> Ptr String -> io ()
setBufBase p s = primIO $ prim__uv_set_buf_base p s

export %inline
getBufLen : HasIO io => Ptr Buf -> io Bits32
getBufLen p = primIO $ prim__uv_get_buf_len p

export %inline
getBufBase : HasIO io => Ptr Buf -> io (Ptr String)
getBufBase p = primIO $ prim__uv_get_buf_base p

export %inline
initBuf : HasIO io => Ptr Buf -> Ptr String -> Bits32 -> io ()
initBuf buf dat len = primIO $ prim__uv_init_buf buf dat len

||| Allocates a char array of the given length, wrapping it
||| in an `uv_buf_t` that's being initialized.
export
mallocBuf : HasIO io => Bits32 -> io (Ptr Buf)
mallocBuf size = do
  dat <- mallocPtrs String size
  buf <- mallocPtr Buf
  initBuf buf dat size
  pure buf

||| Frees the memory allocated for a `uv_buf_t`'s `base` field.
export %inline
freeBufBase : HasIO io => Ptr Buf -> io ()
freeBufBase buf = getBufBase buf >>= freePtr

||| Frees the memory allocated for a `uv_buf_t`'s `base` field
||| as well as the pointer itself.
|||
||| Use this to release a `Ptr Buf` allocated with `mallocBuf`.
export %inline
freeBuf : HasIO io => Ptr Buf -> io ()
freeBuf buf = freeBufBase buf >> freePtr buf

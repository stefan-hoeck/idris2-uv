module System.UV.Raw.Pointer

import Data.Buffer
import Derive.Prelude
import System.UV.Raw.Util
import public System.FFI

%language ElabReflection
%default total

--------------------------------------------------------------------------------
-- Buffers
--------------------------------------------------------------------------------

export
data Buf : Type where

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "scheme:blodwen-new-buffer"
         "RefC:newBuffer"
         "node:lambda:s=>Buffer.alloc(s)"
prim__newBuffer : Bits32 -> PrimIO Buffer

%foreign (idris_uv "uv_set_buf_len")
uv_set_buf_len : Ptr Buf -> Bits32 -> PrimIO ()

%foreign (idris_uv "uv_set_buf_base")
uv_set_buf_base : Ptr Buf -> Ptr Bits8 -> PrimIO ()

%foreign (idris_uv "uv_get_buf_len")
uv_get_buf_len : Ptr Buf -> PrimIO Bits32

%foreign (idris_uv "uv_get_buf_base")
uv_get_buf_base : Ptr Buf -> PrimIO (Ptr Bits8)

%foreign (idris_uv "uv_init_buf")
uv_init_buf : Bits32 -> PrimIO (Ptr Buf)

%foreign (idris_uv "uv_copy_buf")
uv_copy_to_buf : Ptr Bits8 -> Buffer -> Bits32 -> PrimIO ()

%foreign (idris_uv "uv_copy_buf")
uv_copy_from_buf : Buffer -> Ptr Bits8 -> Bits32 -> PrimIO ()

%foreign "scheme:blodwen-buffer-getstring"
uv_get_string : Ptr Bits8 -> (offset, len : Bits32) -> PrimIO String

export %foreign (idris_uv "uv_async_sz")
uv_async_sz : Bits32

export %foreign (idris_uv "uv_check_sz")
uv_check_sz : Bits32

export %foreign (idris_uv "uv_fs_event_sz")
uv_fs_event_sz : Bits32

export %foreign (idris_uv "uv_fs_poll_sz")
uv_fs_poll_sz : Bits32

export %foreign (idris_uv "uv_handle_sz")
uv_handle_sz : Bits32

export %foreign (idris_uv "uv_idle_sz")
uv_idle_sz : Bits32

export %foreign (idris_uv "uv_named_pipe_sz")
uv_namedpipe_sz : Bits32

export %foreign (idris_uv "uv_poll_sz")
uv_poll_sz : Bits32

export %foreign (idris_uv "uv_prepare_sz")
uv_prepare_sz : Bits32

export %foreign (idris_uv "uv_process_sz")
uv_process_sz : Bits32

export %foreign (idris_uv "uv_stream_sz")
uv_stream_sz : Bits32

export %foreign (idris_uv "uv_tcp_sz")
uv_tcp_sz : Bits32

export %foreign (idris_uv "uv_timer_sz")
uv_timer_sz : Bits32

export %foreign (idris_uv "uv_tty_sz")
uv_tty_sz : Bits32

export %foreign (idris_uv "uv_udp_sz")
uv_udp_sz : Bits32

export %foreign (idris_uv "uv_signal_sz")
uv_signal_sz : Bits32

export %foreign (idris_uv "uv_req_sz")
uv_req_sz : Bits32

export %foreign (idris_uv "uv_connect_sz")
uv_connect_sz : Bits32

export %foreign (idris_uv "uv_write_sz")
uv_write_sz : Bits32

export %foreign (idris_uv "uv_shutdown_sz")
uv_shutdown_sz : Bits32

export %foreign (idris_uv "uv_upd_send_sz")
uv_upd_send_sz : Bits32

export %foreign (idris_uv "uv_fs_sz")
uv_fs_sz : Bits32

export %foreign (idris_uv "uv_work_sz")
uv_work_sz : Bits32

export %foreign (idris_uv "uv_getaddrinfo_sz")
uv_getaddrinfo_sz : Bits32

export %foreign (idris_uv "uv_getnameinfo_sz")
uv_getnameinfo_sz : Bits32

export %foreign (idris_uv "uv_sockaddr_in_sz")
uv_sockaddr_in_sz : Bits32

export %foreign (idris_uv "uv_sockaddr_in6_sz")
uv_sockaddr_in6_sz : Bits32

export %foreign (idris_uv "uv_sockaddr_sz")
uv_sockaddr_sz : Bits32

export %foreign (idris_uv "uv_addrinfo_sz")
uv_addrinfo_sz : Bits32

export %foreign (idris_uv "uv_buf_sz")
uv_buf_sz : Bits32

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

||| Proof that we have an associated size for a pointer type. This
||| allows us to allocate the correct amount of memory when we need a
||| new pointer of the given type (see `mallocPtr` and `mallocPtrs`).
public export
data PSize : (a : Type) -> (s : Bits32) -> Type where
  [search a]
  ASYNC          : PSize Async Pointer.uv_async_sz
  CHECK          : PSize Check Pointer.uv_check_sz
  FS_EVENT       : PSize FsEvent Pointer.uv_fs_event_sz
  FS_POLL        : PSize FsPoll Pointer.uv_fs_poll_sz
  HANDLE         : PSize Handle Pointer.uv_handle_sz
  IDLE           : PSize Idle Pointer.uv_idle_sz
  NAMEDPIPE      : PSize Pipe Pointer.uv_namedpipe_sz
  POLL           : PSize Poll Pointer.uv_poll_sz
  PREPARE        : PSize Prepare Pointer.uv_prepare_sz
  PROCESS        : PSize Process Pointer.uv_process_sz
  STREAM         : PSize Stream Pointer.uv_stream_sz
  TCP            : PSize Tcp Pointer.uv_tcp_sz
  TIMER          : PSize Timer Pointer.uv_timer_sz
  TTY            : PSize Tty Pointer.uv_tty_sz
  UDP            : PSize Udp Pointer.uv_udp_sz
  SIGNAL         : PSize Signal Pointer.uv_signal_sz
  REQ            : PSize Req Pointer.uv_req_sz
  CONNECT        : PSize Connect Pointer.uv_connect_sz
  WRITE          : PSize Write Pointer.uv_write_sz
  SHUTDOWN       : PSize Shutdown Pointer.uv_shutdown_sz
  FS             : PSize Fs Pointer.uv_fs_sz
  WORK           : PSize Work Pointer.uv_work_sz
  GETADDRINFO    : PSize GetAddrInfo Pointer.uv_getaddrinfo_sz
  GETNAMEINFO    : PSize GetNameInfo Pointer.uv_getnameinfo_sz
  ADDRINFO       : PSize AddrInfo Pointer.uv_addrinfo_sz
  SOCKADDR       : PSize SockAddr Pointer.uv_sockaddr_sz
  SOCKADDRIN     : PSize SockAddrIn Pointer.uv_sockaddr_in_sz
  SOCKADDRIN6    : PSize SockAddrIn6 Pointer.uv_sockaddr_in6_sz
  BUF            : PSize Buf Pointer.uv_buf_sz
  BYTE           : PSize Bits8 1
  CHAR           : PSize Char 1

%runElab deriveIndexed "PSize" [Show]

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

||| Frees a typed pointer.
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
|||
||| This data type is a proof of such a subtyping relation. Use `castPtr`
||| to safely convert pointers.
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
  ByteChar             : PCast Bits8 Char
  CharByte             : PCast Char Bits8

export
castPtr : (0 _ : PCast s t) => Ptr s -> Ptr t
castPtr = believe_me

--------------------------------------------------------------------------------
-- Buffers
--------------------------------------------------------------------------------

export %inline
newBuffer : HasIO io => Bits32 -> io Buffer
newBuffer s = primIO $ prim__newBuffer s

export %inline
setBufLen : HasIO io => Ptr Buf -> Bits32 -> io ()
setBufLen p s = primIO $ uv_set_buf_len p s

export %inline
setBufBase : HasIO io => Ptr Buf -> Ptr Bits8 -> io ()
setBufBase p s = primIO $ uv_set_buf_base p s

export %inline
getBufLen : HasIO io => Ptr Buf -> io Bits32
getBufLen p = primIO $ uv_get_buf_len p

export %inline
getBufBase : HasIO io => Ptr Buf -> io (Ptr Bits8)
getBufBase p = primIO $ uv_get_buf_base p

export %inline
initBuf : HasIO io => Bits32 -> io (Ptr Buf)
initBuf len = primIO $ uv_init_buf len

||| Allocates a char array of the given length, wrapping it
||| in an `uv_buf_t` that's being initialized.
export
mallocBuf : HasIO io => Bits32 -> io (Ptr Buf)
mallocBuf size = do
  buf  <- initBuf size
  blen <- getBufLen buf
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

||| Copy the given number of bytes from a `uv_buf_t` to an Idris-managed
||| buffer.
export
copyToBuffer : HasIO io => Ptr Buf -> Buffer -> Bits32 -> io ()
copyToBuffer p buf x = do
  pchar <- getBufBase p
  primIO $ uv_copy_to_buf pchar buf x

||| Copy the given number of bytes an Idris-managed
||| buffer to a `uv_buf_t`.
export
copyFromBuffer : HasIO io => Buffer -> Ptr Buf -> Bits32 -> io ()
copyFromBuffer buf p x = do
  pchar <- getBufBase p
  len   <- getBufLen p
  primIO $ uv_copy_from_buf buf pchar x

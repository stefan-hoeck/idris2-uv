module System.UV.Raw.Pointer

import Data.Buffer
import Derive.Prelude
import System.UV.Raw.Util
import public System.FFI
import public System.UV.Data.Pointer

%language ElabReflection
%default total

--------------------------------------------------------------------------------
-- Buffers and Loops
--------------------------------------------------------------------------------

export
data Buf : Type where

export
data Loop : Type where

||| Convert a `Ptr Char` to an Idris string.
|||
||| Note: Users must make sure that the given pointer points at a
||| zero-terminated byte array. As an alternative, consider converting
||| a `Ptr Bits8`.
export %inline
getString : Ptr Char -> String
getString p = prim__getString (believe_me p)

||| Like `getString` but returns `Nothing` in case the given pointer is the
||| null pointer.
export %inline
getStringMay : Ptr Char -> Maybe String
getStringMay p =
  case prim__nullPtr p of
    0 => Just $ getString p
    _ => Nothing

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

%foreign (idris_uv "uv_copy_buf")
uv_copy_to_buf : Ptr Bits8 -> Buffer -> Bits32 -> PrimIO ()

%foreign (idris_uv "uv_copy_from_buf")
uv_copy_from_buf : Buffer -> Ptr Bits8 -> (size, offset : Bits32) -> PrimIO ()

%foreign "scheme:blodwen-buffer-getstring"
uv_get_string : Ptr Bits8 -> (offset, len : Bits32) -> PrimIO String

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
  ASYNC          : PSize Async SZ_ASYNC
  CHECK          : PSize Check SZ_CHECK
  FS_EVENT       : PSize FsEvent SZ_FS_EVENT
  FS_POLL        : PSize FsPoll SZ_FS_POLL
  HANDLE         : PSize Handle SZ_HANDLE
  IDLE           : PSize Idle SZ_IDLE
  NAMEDPIPE      : PSize Pipe SZ_NAMED_PIPE
  POLL           : PSize Poll SZ_POLL
  PREPARE        : PSize Prepare SZ_PREPARE
  PROCESS        : PSize Process SZ_PROCESS
  STREAM         : PSize Stream SZ_STREAM
  TCP            : PSize Tcp SZ_TCP
  TIMER          : PSize Timer SZ_TIMER
  TTY            : PSize Tty SZ_TTY
  UDP            : PSize Udp SZ_UDP
  SIGNAL         : PSize Signal SZ_SIGNAL
  REQ            : PSize Req SZ_REQ
  CONNECT        : PSize Connect SZ_CONNECT
  WRITE          : PSize Write SZ_WRITE
  SHUTDOWN       : PSize Shutdown SZ_SHUTDOWN
  FS             : PSize Fs SZ_FS
  WORK           : PSize Work SZ_WORK
  GETADDRINFO    : PSize GetAddrInfo SZ_GETADDRINFO
  GETNAMEINFO    : PSize GetNameInfo SZ_GETNAMEINFO
  ADDRINFO       : PSize AddrInfo SZ_ADDRINFO
  SOCKADDR       : PSize SockAddr SZ_SOCKADDR
  SOCKADDRIN     : PSize SockAddrIn SZ_SOCKADDR_IN
  SOCKADDRIN6    : PSize SockAddrIn6 SZ_SOCKADDR_IN6
  BUF            : PSize Buf SZ_BUF
  LOOP           : PSize Loop SZ_LOOP
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
  ConnectReq           : PCast Connect Req
  WriteReq             : PCast Write Req
  ShutdownReq          : PCast Shutdown Req
  UpdSendReq           : PCast UpdSend Req
  FsReq                : PCast Fs Req
  WorkReq              : PCast Work Req
  GetAddrInfoReq       : PCast GetAddrInfo Req
  GetNameInfoReq       : PCast GetNameInfo Req
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
getBufLen : HasIO io => Ptr Buf -> io Bits32
getBufLen p = primIO $ uv_get_buf_len p

export %inline
setBufBase : HasIO io => Ptr Buf -> Ptr Bits8 -> io ()
setBufBase p s = primIO $ uv_set_buf_base p s

export %inline
getBufBase : HasIO io => Ptr Buf -> io (Ptr Bits8)
getBufBase p = primIO $ uv_get_buf_base p

export
initBuf : HasIO io => Ptr Buf -> Ptr Bits8 -> Bits32 -> io ()
initBuf pbuf pcs len = do
  setBufBase pbuf pcs
  setBufLen pbuf len

||| Frees the memory allocated for a `uv_buf_t`'s `base` field.
export %inline
freeBufBase : HasIO io => Ptr Buf -> io ()
freeBufBase buf = getBufBase buf >>= freePtr

||| Copy the given number of bytes from a byte array to an Idris-managed
||| buffer.
export
copyToBuffer : HasIO io => Ptr Bits8 -> Buffer -> Bits32 -> io ()
copyToBuffer p buf x = primIO $ uv_copy_to_buf p buf x

||| Copy the given number of bytes from a byte array to an Idris-managed
||| buffer.
export
copyBufToBuffer : HasIO io => Ptr Buf -> Buffer -> Bits32 -> io ()
copyBufToBuffer p buf s = getBufBase p >>= \x => copyToBuffer x buf s

||| Copy the given number of bytes an Idris-managed
||| buffer to a `Ptr Char`
export
copyFromBuffer : HasIO io => Buffer -> (size, offset : Bits32) -> io (Ptr Bits8)
copyFromBuffer buf size offset = do
  pchar <- mallocPtrs Bits8 size
  primIO $ uv_copy_from_buf buf pchar size offset
  pure pchar

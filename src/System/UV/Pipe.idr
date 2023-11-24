module System.UV.Pipe

import Data.Buffer
import System.FFI
import System.UV.Error
import System.UV.File
import System.UV.Handle
import System.UV.Loop
import System.UV.Pointer
import System.UV.Util

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_pipe_init")
prim__uv_pipe_init : Ptr LoopPtr -> Ptr Pipe -> (ipc : Int32) -> PrimIO Int32

%foreign (idris_uv "uv_pipe_open")
prim__uv_pipe_open : Ptr Pipe -> (file : Int32) -> PrimIO Int32

%foreign (idris_uv "uv_pipe_bind")
prim__uv_pipe_bind : Ptr Pipe -> String -> PrimIO Int32

%foreign (idris_uv "uv_pipe_connect")
prim__uv_pipe_connect :
     Ptr Connect
  -> Ptr Pipe
  -> String
  -> (Ptr Connect -> Int32 -> PrimIO ())
  -> PrimIO ()

%foreign (idris_uv "uv_pipe_getsockname")
prim__uv_pipe_getsockname : Ptr Pipe -> Buffer -> Bits32 -> PrimIO Int32

%foreign (idris_uv "uv_pipe_getpeername")
prim__uv_pipe_getpeername : Ptr Pipe -> Buffer -> Bits32 -> PrimIO Int32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Initialize a pipe handle. The ipc argument is a boolean to indicate
||| if this pipe will be used for handle passing between processes
||| (which may change the bytes on the wire). Only a connected pipe that will
||| be passing the handles should have this flag set, not the listening
||| pipe that uv_accept is called on.
export %inline
pipeInit : (l : Loop) => Ptr Pipe -> (ipc : Bool) -> UVIO ()
pipeInit p ipc = primUV $ prim__uv_pipe_init l.loop p (boolToInt32 ipc)

||| Open an existing file descriptor or HANDLE as a pipe.
|||
||| The passed file descriptor or HANDLE is not checked for its type,
||| but it's required that it represents a valid pipe.
export %inline
pipeOpen : Ptr Pipe -> File -> UVIO ()
pipeOpen p f = primUV $ prim__uv_pipe_open p f.file

||| Bind the pipe to a file path (Unix) or a name (Windows).
||| 
||| Does not support Linux abstract namespace sockets, unlike uv_pipe_bind2().
||| 
||| Alias for uv_pipe_bind2(handle, name, strlen(name), 0).
||| 
||| NOTE:
|||    Paths on Unix get truncated to sizeof(sockaddr_un.sun_path) bytes,
|||    typically between 92 and 108 bytes.
export %inline
pipebind : Ptr Pipe -> String -> UVIO ()
pipebind p f = primUV $ prim__uv_pipe_bind p f


||| Connect to the Unix domain socket or the Windows named pipe.
||| 
||| Does not support Linux abstract namespace sockets, unlike uv_pipe_connect2().
||| 
||| Alias for uv_pipe_connect2(req, handle, name, strlen(name), 0, cb).
||| 
||| NOTE:
|||    Paths on Unix get truncated to sizeof(sockaddr_un.sun_path) bytes,
|||    typically between 92 and 108 bytes.
export %inline
pipeConnect :
     {auto has : HasIO io}
  -> Ptr Connect
  -> Ptr Pipe
  -> String
  -> (Ptr Connect -> Int32 -> IO ())
  -> io ()
pipeConnect pc pp name act =
  primIO $ prim__uv_pipe_connect pc pp name $ \p,res => toPrim (act p res)

||| Get the name of the Unix domain socket or the named pipe.
||| 
||| A  preallocated buffer must be provided. The size parameter holds the length
||| of the buffer and it's set to the number of bytes written to the buffer on output.
||| If the buffer is not big enough UV_ENOBUFS will be returned
||| and len will contain the required size.
||| 
||| Changed in version 1.3.0: the returned length no longer includes the terminating null byte,
|||                           and the buffer is not null terminated.
|||
||| TODO: Use Ptr Buf
export %inline
pipeGetSockName : Ptr Pipe -> Buffer -> Bits32 -> UVIO ()
pipeGetSockName pp buf size = primUV $ prim__uv_pipe_getsockname pp buf size

||| Get the name of the Unix domain socket or the named pipe to which
||| the handle is connected.
||| 
||| A preallocated buffer must be provided. The size parameter holds the
||| length of the buffer and it's set to the number of bytes written
||| to the buffer on output. If the buffer is not big enough UV_ENOBUFS will be  returned
||| and len will contain the required size.
||| 
||| New in version 1.3.0.
|||
||| TODO: Use Ptr Buf
export %inline
pipeGetPeerName : Ptr Pipe -> Buffer -> Bits32 -> UVIO ()
pipeGetPeerName pp buf size = primUV $ prim__uv_pipe_getpeername pp buf size

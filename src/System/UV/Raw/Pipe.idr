module System.UV.Raw.Pipe

import System.UV.Raw.Callback
import System.UV.Raw.Handle
import System.UV.Raw.Req
import System.UV.Raw.Loop
import System.UV.Raw.Pointer
import System.UV.Raw.Util

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_pipe_init")
prim__uv_pipe_init : Ptr Loop -> Ptr Pipe -> (ipc : Int32) -> PrimIO Int32

%foreign (idris_uv "uv_pipe_open")
prim__uv_pipe_open : Ptr Pipe -> (file : Int32) -> PrimIO Int32

%foreign (idris_uv "uv_pipe_bind")
prim__uv_pipe_bind : Ptr Pipe -> String -> PrimIO Int32

%foreign (idris_uv "uv_pipe_connect")
prim__uv_pipe_connect : Ptr Connect -> Ptr Pipe -> String -> AnyPtr -> PrimIO ()

%foreign (idris_uv "uv_pipe_getsockname")
prim__uv_pipe_getsockname : Ptr Pipe -> Ptr Char -> Ptr Bits32 -> PrimIO Int32

%foreign (idris_uv "uv_pipe_getpeername")
prim__uv_pipe_getpeername : Ptr Pipe -> Ptr Char -> Ptr Bits32 -> PrimIO Int32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

parameters {auto has : HasIO io}

  ||| Initialize a pipe handle. The ipc argument is a boolean to indicate
  ||| if this pipe will be used for handle passing between processes
  ||| (which may change the bytes on the wire). Only a connected pipe that will
  ||| be passing the handles should have this flag set, not the listening
  ||| pipe that uv_accept is called on.
  export %inline
  uv_pipe_init : Ptr Loop -> Ptr Pipe -> (ipc : Bool) -> io Int32
  uv_pipe_init l p ipc = primIO $ prim__uv_pipe_init l p (boolToInt32 ipc)

  ||| Open an existing file descriptor or HANDLE as a pipe.
  |||
  ||| The passed file descriptor or HANDLE is not checked for its type,
  ||| but it's required that it represents a valid pipe.
  export %inline
  uv_pipe_open : Ptr Pipe -> Int32 -> io Int32
  uv_pipe_open p f = primIO $ prim__uv_pipe_open p f

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
  uv_pipe_bind : Ptr Pipe -> String -> io Int32
  uv_pipe_bind p f = primIO $ prim__uv_pipe_bind p f


  ||| Connect to the Unix domain socket or the Windows named pipe.
  |||
  ||| Does not support Linux abstract namespace sockets, unlike uv_pipe_connect2().
  |||
  ||| Alias for uv_pipe_connect2(req, handle, name, strlen(name), 0, cb).
  |||
  ||| NOTE:
  |||    Paths on Unix get truncated to sizeof(sockaddr_un.sun_path) bytes,
  |||    typically between 92 and 108 bytes.
  export
  uv_pipe_connect :
       Ptr Pipe
    -> String
    -> (Ptr Connect -> Int32 -> IO ())
    -> io ()
  uv_pipe_connect pp name act = do
    pc <- mallocPtr Connect
    cb <- ptrIntCB (\x,y => act x y >> freeReq x)
    uv_req_set_data pc cb
    primIO $ prim__uv_pipe_connect pc pp name cb

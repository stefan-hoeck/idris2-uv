module System.UV.Pipe

import Data.Buffer.Indexed

import System.UV.Async
import System.UV.File
import System.UV.Loop
import System.UV.Pointer
import System.UV.Resource
import System.UV.Stream
import System.UV.Util
import System.UV.Raw.Handle
import public System.UV.Raw.Pipe

export
Resource (Ptr Pipe) where
  release h = uv_close h freePtr

%default total

parameters {auto l : UVLoop}
           {auto has : Has UVError es}

  export
  mkPipe : Bool -> Async es (Cancel, Ptr Pipe)
  mkPipe b = do
    pp <- mallocPtr Pipe >>= uvAct (\x => uv_pipe_init l.loop x b)
    c  <- mkCancel (release pp)
    pure (c, pp)

  export
  pipeOpen : File -> Async es (Cancel, Ptr Pipe)
  pipeOpen f = do
    (c,pp) <- mkPipe False
    uv $ uv_pipe_open pp f.file
    pure (c,pp)

  export %inline
  stdinOpen : Async es(Cancel, Ptr Pipe)
  stdinOpen = pipeOpen stdin

  -- export %inline
  -- streamStdin : (l : UVLoop) => Source [UVError] ByteString
  -- streamStdin = stdinOpen |> flatMap (\(io,p) => streamRead 0xffff p io)

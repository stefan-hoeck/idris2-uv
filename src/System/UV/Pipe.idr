module System.UV.Pipe

import Data.Buffer.Indexed

import IO.Async.Event
import System.UV.File
import System.UV.Loop
import System.UV.Pointer
import System.UV.Stream
import System.UV.Raw.Stream
import System.UV.Util
import System.UV.Raw.Handle
import System.UV.Raw.Pipe

%default total

export %inline
(cc : CloseCB) => Resource (Ptr Pipe) where
  release h = uv_close h cc

parameters {auto l : UVLoop}
           {auto has : Has UVError es}

  export
  mkPipe : Bool -> Async es (Ptr Pipe)
  mkPipe b = mallocPtr Pipe >>= uvAct (\x => uv_pipe_init l.loop x b)

  export
  pipeOpen : File -> Async es (Ptr Pipe)
  pipeOpen f = do
    pp <- mkPipe False
    uv $ uv_pipe_open pp f.file
    pure pp

  export %inline
  stdinOpen : Async es (Ptr Pipe)
  stdinOpen = pipeOpen stdin

  export
  streamStdin :
       AllocCB
    -> (Buffer (ReadRes ByteString) -> Async es a)
    -> Async es a
  streamStdin ac run = use1 stdinOpen $ \h => read ac h run

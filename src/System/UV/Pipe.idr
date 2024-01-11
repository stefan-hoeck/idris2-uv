module System.UV.Pipe

import Data.Buffer.Indexed

import System.UV.File
import System.UV.Loop
import System.UV.Pointer
import System.UV.Stream
import System.UV.Util
import System.UV.Raw.Handle
import System.UV.Raw.Pipe

-- %default total
--
-- export
-- Resource (Ptr Pipe) where
--   release h = uv_close h freePtr
--
-- parameters {auto l : UVLoop}
--            {auto has : Has UVError es}
--
--   export
--   mkPipe : Bool -> Async es (Ptr Pipe)
--   mkPipe b = mallocPtr Pipe >>= uvAct (\x => uv_pipe_init l.loop x b)
--
--   export
--   pipeOpen : File -> Async es (Ptr Pipe)
--   pipeOpen f = do
--     pp <- mkPipe False
--     uv $ uv_pipe_open pp f.file
--     pure pp
--
--   export %inline
--   stdinOpen : Async es (Ptr Pipe)
--   stdinOpen = pipeOpen stdin
--
--   export covering
--   streamStdin :
--        (ReadRes ByteString -> Async es (Maybe a))
--     -> Async es (Fiber es a)
--   streamStdin run = use1 stdinOpen $ \h => streamRead 0xffff h run

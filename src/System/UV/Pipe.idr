module System.UV.Pipe

import Data.Buffer.Indexed

import System.UV.Async
import System.UV.File
import System.UV.Loop
import System.UV.Pointer
import System.UV.Resource
import System.UV.Stream
import System.UV.Util
import public System.UV.Raw.Pipe

%default total

-- export
-- pipeOpen : (l : UVLoop) => File -> Source [UVError] (IO (), Ptr Pipe)
-- pipeOpen f =
--   lift1 $ do
--     pipe <- mallocPtr Pipe
--     r1   <- uv_pipe_init l.loop pipe False
--     r2   <- uv_pipe_open pipe f.file
--     case uvRes r1 >> uvRes r2 of
--       Left err => releaseHandle pipe $> Left (inject err)
--       Right () => pure $ Right (releaseHandle pipe, pipe)
--
-- export %inline
-- stdinOpen : (l : UVLoop) => Source [UVError] (IO (), Ptr Pipe)
-- stdinOpen = pipeOpen stdin
--
-- covering export %inline
-- streamStdin : (l : UVLoop) => Source [UVError] ByteString
-- streamStdin = stdinOpen |> flatMap (\(io,p) => streamRead 0xffff p io)
--

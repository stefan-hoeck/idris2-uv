module System.UV.Work

import Data.Buffer.Indexed
import Data.ByteString
import Data.ByteVect
import Data.DPair
import Data.IORef
import Data.Maybe

import System.Rx.Core
import System.Rx.Msg
import System.Rx.Sink
import System.Rx.Source

import System.UV.Error
import System.UV.Handle
import System.UV.Loop
import System.UV.Pointer
import System.UV.Timer
import System.UV.Raw.Work
import System

%default total

mapMsg : (List a -> List b) -> (m : Msg es a) -> Msg es b
mapMsg f (Next vals) = Next $ f vals
mapMsg f (Done vals) = Done $ f vals
mapMsg f (Err err)   = Err err

-- implementation of the downstream side of a synchronous pipe
parSrc : (l : UVLoop) => SinkRef es a -> (List a -> List b) -> Src es b
parSrc ref f Nothing  = close ref
parSrc ref f (Just g) = request ref $ \m1 => do
  pa <- mallocPtr Async
  ti <- mallocPtr Timer
  ignore $ uv_timer_init l.loop ti
  ignore $ fork $ do
    m2 <- pure (mapMsg f m1)
    uv_async_init_and_send l.loop pa $ \x => do
      releaseHandle x
      releaseHandle ti
      when (isTerminal m1) (abort ref) -- upstream terminated, release resources
      when (isTerminal m2) (close ref) -- we terminated, send `Nothing` upstream
      g m2

||| Synchronous, sequential, and potentially effectful conversion
||| of messages.
|||
||| Since the result is of type `ValidAfter m fs b`, we can do error
||| handling here and we can abort early, but we cannot continue after
||| upstream has terminated.
|||
||| Most simple, sequential pipes are implemented via this function.
export
parMap : UVLoop => (f : List a -> List b) -> Pipe es es a b
parMap f = MkPipe $ do
  ref  <- sinkRef es a (pure ())
  pure (sink ref, parSrc ref f)

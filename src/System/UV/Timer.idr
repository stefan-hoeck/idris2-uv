||| This module provides functions for running computations
||| once or more at discrete time intervals.
|||
||| This provides a layer of abstraction and security on top
||| of module `System.UV.Timer.Raw`.
module System.UV.Timer

import Data.IORef
import System.Rx.Core
import System.UV.Error
import System.UV.Handle
import System.UV.Loop
import System.UV.Pointer
import System.UV.Resource
import public System.UV.Raw.Timer

%default total

||| Sends a signal every `repeat` milliseconds, the first time
||| after `timeout` has passed.
export
timer : (l : UVLoop) => (timeout,repeat : Bits64) -> Source [UVError] ()
timer t r = MkSource $ do
  cb <- cbRef [UVError] ()
  h  <- mallocPtr Timer
  Right () <- uvRes <$> uv_timer_init l.loop h
    | Left e => releaseHandle h >> pure (fail e)
  Right () <- uvRes <$> uv_timer_start h (\_ => send cb (Next [()])) t r
    | Left e => releaseHandle h >> pure (fail e)
  pure (toSrc cb $ releaseHandle h)

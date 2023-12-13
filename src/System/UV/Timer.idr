||| This module provides functions for running computations
||| once or more at discrete time intervals.
|||
||| This provides a layer of abstraction and security on top
||| of module `System.UV.Timer.Raw`.
module System.UV.Timer

import System.Rx
import System.UV.Error
import System.UV.Handle
import System.UV.Loop
import System.UV.Pointer
import public System.UV.Raw.Timer

%default total

||| Sends a signal every `repeat` milliseconds, the first time
||| after `timeout` has passed.
export
timer : (l : UVLoop) => (timeout,repeat : Bits64) -> Source [UVError] ()
timer t r = MkSource $ do
  h   <- mallocPtr Timer
  ref <- sourceRef [UVError] () (releaseHandle h)
  r1 <- uv_timer_init l.loop h
  r2 <- uv_timer_start h (\_ => emit1 ref ()) t r
  case uvRes r1 >> uvRes r2 of
    Left e   => error ref e
    Right () => pure ()
  pure $ hotSrc ref

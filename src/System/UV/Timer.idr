||| This module provides functions for running computations
||| once or more at discrete time intervals.
|||
||| This provides a layer of abstraction and security on top
||| of module `System.UV.Timer.Raw`.
module System.UV.Timer

import System.UV.Async
import System.UV.Error
import System.UV.Loop
import System.UV.Pointer
import System.UV.Raw.Handle
import System.UV.Raw.Timer
import System.UV.Resource

%default total

export
Resource (Ptr Timer) where
  release h = uv_close h freePtr

parameters {auto l   : UVLoop}
           {auto has : Has UVError es}
  export
  mkTimer : Async es (Cancel, Ptr Timer)
  mkTimer = do
    pt <- mallocPtr Timer >>= uvAct (uv_timer_init l.loop)
    c  <- mkCancel (ignore (uv_timer_stop pt) >> release pt)
    pure (c, pt)

  ||| Sends a signal every `repeat` milliseconds, the first time
  ||| after `timeout` has passed.
  export
  repeatedly :
       (timeout,repeat : Bits64)
    -> (Cancel -> Async [] ())
    -> Async es Cancel
  repeatedly t r run = do
    (c,pt) <- mkTimer
    uvPar c run $ \cb => uv_timer_start pt (\_ => cb c) t r

  ||| Sends a signal after `timeout` has passed.
  export
  once : (timeout : Bits64) -> Async [] () -> Async es Cancel
  once t run = do
    (c,pt) <- mkTimer
    uvPar1' c run $ \cb => uv_timer_start pt (\_ => cb) t 0

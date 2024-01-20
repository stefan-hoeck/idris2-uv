||| This module provides functions for running computations
||| once or more at discrete time intervals.
|||
||| This provides a layer of abstraction and security on top
||| of module `System.UV.Timer.Raw`.
module System.UV.Timer

import IO.Async.Event
import System.UV.Loop
import System.UV.Pointer
import System.UV.Raw.Handle
import System.UV.Raw.Timer

%default total

%inline stopTimer : HasIO io => Ptr Timer -> io ()
stopTimer = ignore . uv_timer_stop

parameters {auto cc : CloseCB}
  export %inline
  Resource (Ptr Timer) where
    release h = stopTimer h >> uv_close h cc

parameters {auto l   : UVLoop}
           {auto has : Has UVError es}
  export
  mkTimer : Async es (Ptr Timer)
  mkTimer = mallocPtr Timer >>= uvAct (uv_timer_init l.loop)

  ||| Sends a signal every `repeat` milliseconds, the first time
  ||| after `timeout` has passed.
  export
  repeatedly :
       (timeout,repeat : Bits64)
    -> (Event Nat -> Async es a)
    -> Async es a
  repeatedly t r run =
    use1 mkTimer $ \pt => do
      ev <- newEvent
      uv $ uv_timer_start pt (\_ => send ev 1 id (+)) t r
      run ev

  ||| Sends a signal after `timeout` milliseconds have passed.
  export
  sleep : (timeout : Bits64) -> Async es ()
  sleep t = do
    uvCancelableAsync
      mkTimer stopTimer release (\p,cb => uv_timer_start p (\_ => cb ()) t 0)

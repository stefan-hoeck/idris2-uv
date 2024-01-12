||| This module provides functions for running computations
||| once or more at discrete time intervals.
|||
||| This provides a layer of abstraction and security on top
||| of module `System.UV.Timer.Raw`.
module System.UV.Timer

import System.UV.Loop
import System.UV.Pointer
import System.UV.Raw.Handle
import System.UV.Raw.Timer

%default total

parameters {auto cc : CloseCB}
  export %inline
  Resource (Ptr Timer) where
    release h = uv_close h cc

  timer_stop : Ptr Timer -> Async [] ()
  timer_stop pt = ignore (uv_timer_stop pt) >> release pt

parameters {auto l   : UVLoop}
           {auto has : Has UVError es}
  export
  mkTimer : Async es (Ptr Timer)
  mkTimer = mallocPtr Timer >>= uvAct (uv_timer_init l.loop)

  ||| Sends a signal every `repeat` milliseconds, the first time
  ||| after `timeout` has passed.
  export covering
  repeatedly :
       (timeout,repeat : Bits64)
    -> Async es (Maybe a)
    -> Async es (Fiber es a)
  repeatedly t r run = do
    pt <- mkTimer
    uvForever' run pt timer_stop $ \cb => uv_timer_start pt (\_ => cb) t r

  ||| Sends a signal after `timeout` milliseconds have passed.
  export covering
  once : (timeout : Bits64) -> Async es ()
  once t = do
    pt <- mkTimer
    uvOnce' pt timer_stop $ \cb => uv_timer_start pt (\_ => cb) t 0

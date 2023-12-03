||| This module provides functions for running computations
||| once or more at discrete time intervals.
|||
||| This provides a layer of abstraction and security on top
||| of module `System.UV.Timer.Raw`.
module System.UV.Timer

import System.UV.Error
import System.UV.Handle
import System.UV.Loop
import System.UV.Pointer
import public System.UV.Raw.Timer

%default total

parameters {auto l : UVLoop}
           (timeout : Bits64)

  ||| Invokes the given IO action every `repeat` milliseconds, the first time
  ||| after `timeout` has passed.
  |||
  ||| Execution will be stopped when the I/O action returns `False`.
  |||
  ||| If `reference` is set to `False`, the timer handle will not be
  ||| referenced at the event loop: The loop will terminate, if there are
  ||| only unreferenced handles left.
  export
  timer : (repeat : Bits64) -> (reference : Bool) -> IO Bool -> UVIO ()
  timer r ref act = do
    h   <- mallocPtr Timer
    uvio $ uv_timer_init l.loop h
    when (not ref) (uv_unref h)
    uvio $ uv_timer_start h (releaseOnFalse act) timeout r

  ||| Invokes the given IO action every `repeat` milliseconds, the first time
  ||| after `timeout` has passed.
  |||
  ||| See `timer` for an explanation of the `reference` argument.
  export %inline
  repeatedly : (repeat : Bits64) -> (reference : Bool) -> IO () -> UVIO ()
  repeatedly r ref = timer r ref . ($> True)

  ||| Invokes the given IO action once after `timeout` milliseconds.
  |||
  ||| See `timer` for an explanation of the `reference` argument.
  export %inline
  delayed : (timeout : Bits64) -> (reference : Bool) -> IO () -> UVIO ()
  delayed t ref = timer 0 ref . ($> False)

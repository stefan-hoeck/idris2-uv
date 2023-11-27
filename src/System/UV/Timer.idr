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
import System.UV.Resource
import public System.UV.Raw.Timer

%default total

||| Invokes the given IO action every `repeat` milliseconds, the first time
||| after `timeout` has passed.
|||
||| Execution can be stopped whenever the returned `Resource` is released.
||| The release handle is also passed to the callback, so that execution can
||| be stopped from there as well.
export
timer :
     {auto l : Loop}
  -> (timeout,repeat : Bits64)
  -> (Resource -> IO ())
  -> UVIO Resource 
timer t r act = do
  h   <- mallocPtr Timer
  uvio $ uv_timer_init l.loop h
  res <- manageHandle h
  uvio $ uv_timer_start h (\_ => act res) t r
  pure res

||| Invokes the given IO action every `repeat` milliseconds, the first time
||| after `timeout` has passed.
|||
||| Execution can be stopped whenever the returned `Resource` is released.
export %inline
repeatedly : (l : Loop) => (timeout,repeat : Bits64) -> IO () -> UVIO Resource 
repeatedly t r = timer t r . const

||| Invokes the given IO action after `timeout` milliseconds.
|||
||| Execution can be aborted whenever the returned `Resource` is released.
||| Note: All resources are freed automatically
|||       after the IO action has been resolved.
export %inline
delayed : (l : Loop) => (timeout : Bits64) -> IO () -> UVIO Resource 
delayed t act = timer t 0 (\res => act >> release res)

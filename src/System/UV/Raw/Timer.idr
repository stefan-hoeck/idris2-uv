||| This module provides the raw primitive bindings to the
||| timer API from libuv.
|||
||| No additional security measures are implemented. For a nicer but
||| more restrictive API, see module `System.UV.Timer`.
module System.UV.Raw.Timer

import System.UV.Raw.Callback
import System.UV.Raw.Handle
import System.UV.Raw.Loop
import System.UV.Raw.Pointer
import System.UV.Raw.Util

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_timer_init")
prim__uv_timer_init : Ptr Loop -> Ptr Timer -> PrimIO Int32

%foreign (idris_uv "uv_timer_start")
prim__uv_timer_start : Ptr Timer -> AnyPtr -> Bits64 -> Bits64 -> PrimIO Int32

%foreign (idris_uv "uv_timer_stop")
prim__uv_timer_stop : Ptr Timer -> PrimIO Int32

%foreign (idris_uv "uv_timer_set_repeat")
prim__uv_timer_set_repeat : Ptr Timer -> Bits64 -> PrimIO ()

%foreign (idris_uv "uv_timer_get_repeat")
prim__uv_timer_get_repeat : Ptr Timer -> PrimIO Bits64

%foreign (idris_uv "uv_timer_get_due_in")
prim__uv_timer_get_due_in : Ptr Timer -> PrimIO Bits64

%foreign (idris_uv "uv_timer_again")
prim__uv_timer_again : Ptr Timer -> PrimIO Int32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

parameters {auto has : HasIO io}

  ||| Initialize the handle.
  export %inline
  uv_timer_init : Ptr Loop -> Ptr Timer -> io Int32
  uv_timer_init ptr ti = primIO $ prim__uv_timer_init ptr ti

  ||| Start the timer. timeout and repeat are in milliseconds.
  |||
  ||| If timeout is zero, the callback fires on the next
  ||| event loop iteration. If repeat is non-zero, the callback fires
  ||| first after timeout milliseconds and then repeatedly after repeat
  ||| milliseconds.
  export
  uv_timer_start :
       Ptr Timer
    -> (Ptr Timer -> IO ())
    -> (timeout,repeat : Bits64)
    -> io Int32
  uv_timer_start p f t r = do
    cb <- ptrCB f
    uv_handle_set_data p cb
    primIO $ prim__uv_timer_start p cb t r

  ||| Stop the timer, the callback will not be called anymore.
  export %inline
  uv_timer_stop : Ptr Timer -> io Int32
  uv_timer_stop ptr = primIO $ prim__uv_timer_stop ptr

  ||| Stop the timer, and if it is repeating restart it using
  ||| the repeat value as the timeout. If the timer has
  ||| never been started before it returns UV_EINVAL.
  export %inline
  uv_timer_again : Ptr Timer -> io Int32
  uv_timer_again ptr = primIO $ prim__uv_timer_again ptr

  ||| Set the repeat interval value in milliseconds. The timer
  ||| will be scheduled to run on the given interval, regardless
  ||| of the callback execution duration, and will follow normal
  ||| timer semantics in the case of a  time-slice overrun.
  |||
  ||| For  example, if a 50ms repeating timer first runs for 17ms,
  ||| it will be scheduled to run again 33ms later. If other tasks
  ||| consume more than the 33ms following the first timer callback,
  ||| then the callback will run as soon as possible.
  |||
  ||| NOTE:
  |||    If the repeat value is set from a timer callback it does
  |||    not immediately take effect.  If the timer was non-repeating
  |||    before, it will have been stopped. If it was repeating, then the
  |||    old repeat value will  have  been used to schedule the next timeout.
  export %inline
  uv_timer_set_repeat : Ptr Timer -> Bits64 -> io ()
  uv_timer_set_repeat ptr rep = primIO $ prim__uv_timer_set_repeat ptr rep

  ||| Get the timer repeat value.
  export %inline
  uv_timer_get_repeat : Ptr Timer -> io Bits64
  uv_timer_get_repeat ptr = primIO $ prim__uv_timer_get_repeat ptr

  ||| Get the timer due value or 0 if it has expired. The time is relative to
  ||| uv_now.
  export %inline
  uv_timer_get_due_in : Ptr Timer -> io Bits64
  uv_timer_get_due_in ptr = primIO $ prim__uv_timer_get_due_in ptr

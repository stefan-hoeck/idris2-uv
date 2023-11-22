module System.UV.Timer

import Control.Monad.Either
import System.FFI
import System.UV.Error
import System.UV.Handle
import System.UV.Loop
import System.UV.Util

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_timer_init")
prim__uv_timer_init : Ptr LoopPtr -> Ptr Timer -> PrimIO Int64

%foreign (idris_uv "uv_timer_start")
prim__uv_timer_start :
     Ptr Timer
  -> (Ptr Timer -> PrimIO ())
  -> Bits64
  -> Bits64
  -> PrimIO Int64

%foreign (idris_uv "uv_timer_stop")
prim__uv_timer_stop : Ptr Timer -> PrimIO Int64

%foreign (idris_uv "uv_timer_set_repeat")
prim__uv_timer_set_repeat : Ptr Timer -> Bits64 -> PrimIO ()

%foreign (idris_uv "uv_timer_again")
prim__uv_timer_again : Ptr Timer -> PrimIO Int64

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

export %inline
timerInit : Loop => Ptr Timer -> UVIO ()
timerInit @{MkLoop ptr} ti = primUV (prim__uv_timer_init ptr ti)

export %inline
timerStart :
     Ptr Timer
  -> (Ptr Timer -> IO ())
  -> (timeout,repeat : Bits64)
  -> UVIO ()
timerStart ptr f t r =
  primUV $ prim__uv_timer_start ptr (\p => toPrim $ f p) t r

export %inline
timerStop : Ptr Timer -> UVIO ()
timerStop ptr = primUV $ prim__uv_timer_stop ptr

export %inline
timerAgain : Ptr Timer -> UVIO ()
timerAgain ptr = primUV $ prim__uv_timer_again ptr

export %inline
timerSetRepeat : HasIO io => Ptr Timer -> Bits64 -> io ()
timerSetRepeat ptr repeat = primIO $ prim__uv_timer_set_repeat ptr repeat

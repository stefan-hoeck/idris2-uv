module System.UV.Timer

import Control.Monad.Either
import System.UV.Error
import System.UV.Loop
import System.UV.Util

%default total

export
data TimerPtr : Type where

||| Allocated pointer to an `uv_timer_t`.
public export
record Timer where
  [noHints]
  constructor MkTimer
  timer : Ptr TimerPtr

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_init_timer")
prim__initTimer : Ptr LoopPtr -> PrimIO (Ptr TimerPtr)

%foreign (idris_uv "uv_free_timer")
prim__freeTimer : Ptr TimerPtr -> PrimIO ()

%foreign (idris_uv "uv_timer_start")
prim__startTimer :
     Ptr TimerPtr
  -> (Ptr TimerPtr -> PrimIO ())
  -> Bits64
  -> Bits64
  -> PrimIO Int64

%foreign (idris_uv "uv_timer_stop")
prim__stopTimer : Ptr TimerPtr -> PrimIO Int64

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

export %inline
initTimer : Loop => HasIO io => io Timer
initTimer @{MkLoop ptr} = MkTimer <$> primIO (prim__initTimer ptr)

export %inline
startTimer : Timer -> (Timer -> IO ()) -> (timeout,repeat : Bits64) -> UVIO ()
startTimer (MkTimer ptr) f t r =
  primUV $ prim__startTimer ptr (\p => toPrim (f $ MkTimer p)) t r

export
repeatedly : Loop => (timeout,repeat : Bits64) -> IO () -> UVIO Timer
repeatedly t r run = do
  ti <- initTimer
  startTimer ti (const run) t r
  pure ti

export %inline
stopTimer : Timer -> UVIO ()
stopTimer (MkTimer ptr) = primUV $ prim__stopTimer ptr

export %inline
freeTimer : HasIO io => Timer -> io ()
freeTimer (MkTimer ptr) = primIO (prim__freeTimer ptr)

export %inline
endTimer : Timer -> UVIO ()
endTimer ti = stopTimer ti >> freeTimer ti

export %inline
delayed : Loop => Bits64 -> IO () -> UVIO Timer
delayed n = repeatedly n 0

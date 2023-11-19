module System.UV.Timer

import System.UV.Loop
import System.UV.Util

%default total

export
data TimerPtr : Type where

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
  -> PrimIO Int

%foreign (idris_uv "uv_timer_stop")
prim__stopTimer : Ptr TimerPtr -> PrimIO Int

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

parameters {auto has : HasIO io}
  export %inline
  initTimer : Loop => io Timer
  initTimer @{MkLoop ptr} = MkTimer <$> primIO (prim__initTimer ptr)

  export %inline
  startTimer : Timer -> (Timer -> IO ()) -> (timeout,repeat : Bits64) -> io Int
  startTimer (MkTimer ptr) f t r =
    primIO $ prim__startTimer ptr (\p => toPrim (f $ MkTimer p)) t r

  export
  repeatedly : Loop => (timeout,repeat : Bits64) -> IO () -> io Timer
  repeatedly t r run = do
    ti <- initTimer
    ignore $ startTimer ti (const run) t r
    pure ti

  export %inline
  stopTimer : Timer -> io Int
  stopTimer (MkTimer ptr) = primIO $ prim__stopTimer ptr

  export %inline
  freeTimer : Timer -> io ()
  freeTimer (MkTimer ptr) = primIO (prim__freeTimer ptr)

  export %inline
  endTimer : Timer -> io ()
  endTimer ti = ignore (stopTimer ti) >> freeTimer ti

export %inline
delayed : HasIO io => Loop => Bits64 -> IO () -> io Timer
delayed n = repeatedly n 0

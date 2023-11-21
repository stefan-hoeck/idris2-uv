module System.UV.Timer

import Control.Monad.Either
import System.FFI
import System.UV.Error
import System.UV.Loop
import System.UV.Util

%default total

export
data Timer : Type where

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_init_timer")
prim__initTimer : Ptr LoopPtr -> PrimIO (Ptr Timer)

%foreign (idris_uv "uv_timer_start")
prim__startTimer :
     Ptr Timer
  -> (Ptr Timer -> PrimIO ())
  -> Bits64
  -> Bits64
  -> PrimIO Int64

%foreign (idris_uv "uv_timer_stop")
prim__stopTimer : Ptr Timer -> PrimIO Int64

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

%inline
initTimer : Loop => HasIO io => io (Ptr Timer)
initTimer @{MkLoop ptr} = primIO (prim__initTimer ptr)

freeTimer : Ptr Timer -> IO ()
freeTimer ptr = do
  _ <- primIO (prim__stopTimer ptr)
  free $ prim__forgetPtr ptr

%inline
startTimer : Ptr Timer -> IO () -> (timeout,repeat : Bits64) -> UVIO ()
startTimer ptr f t r =
  primUV $ prim__startTimer ptr (\p => toPrim f) t r

export
repeatedly : Loop => (timeout,repeat : Bits64) -> IO () -> UVIO Resource
repeatedly t r run = do
  ti <- initTimer
  startTimer ti run t r
  handle (freeTimer ti)

export
delayed : Loop => Bits64 -> IO () -> UVIO Resource
delayed timeout run = do
  ti <- initTimer
  re <- handle (freeTimer ti)
  startTimer ti (run >> release re) timeout 0
  pure re

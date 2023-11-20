module System.UV.Signal

import Control.Monad.Either
import Derive.Prelude
import System.UV.Error
import System.UV.Loop
import System.UV.Util

%default total
%language ElabReflection

export
data SignalPtr : Type where

||| Allocated pointer to an `uv_signal_t`.
public export
record Signal where
  [noHints]
  constructor MkSignal
  signal : Ptr SignalPtr

||| Signalcodes we can react on.
public export
data SigCode : Type where
  SIGABRT : SigCode
  SIGFPE  : SigCode
  SIGHUP  : SigCode
  SIGILL  : SigCode
  SIGINT  : SigCode
  SIGQUIT : SigCode
  SIGSEGV : SigCode
  SIGTRAP : SigCode
  SIGUSR1 : SigCode
  SIGUSR2 : SigCode

%runElab derive "SigCode" [Show,Eq,Ord]

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_init_signal")
prim__initSignal : Ptr LoopPtr -> PrimIO (Ptr SignalPtr)

%foreign (idris_uv "uv_free_signal")
prim__freeSignal : Ptr SignalPtr -> PrimIO ()

%foreign (idris_uv "uv_signal_start")
prim__startSignal :
     Ptr SignalPtr
  -> (Ptr SignalPtr -> Int64 -> PrimIO ())
  -> Int64
  -> PrimIO Int64

%foreign (idris_uv "uv_signal_stop")
prim__stopSignal : Ptr SignalPtr -> PrimIO Int64

%foreign (idris_uv "uv_sigabrt")
prim__SIGABRT : Int64

%foreign (idris_uv "uv_sigfpe")
prim__SIGFPE  : Int64

%foreign (idris_uv "uv_sighup")
prim__SIGHUP  : Int64

%foreign (idris_uv "uv_sigill")
prim__SIGILL  : Int64

%foreign (idris_uv "uv_sigint")
prim__SIGINT  : Int64

%foreign (idris_uv "uv_sigquit")
prim__SIGQUIT : Int64

%foreign (idris_uv "uv_sigsegv")
prim__SIGSEGV : Int64

%foreign (idris_uv "uv_sigtrap")
prim__SIGTRAP : Int64

%foreign (idris_uv "uv_sigusr1")
prim__SIGUSR1 : Int64

%foreign (idris_uv "uv_sigusr2")
prim__SIGUSR2 : Int64

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Converts a `SigCode` to the corresponding C constant.
export
code : SigCode -> Int64
code SIGABRT = prim__SIGABRT
code SIGFPE  = prim__SIGFPE
code SIGHUP  = prim__SIGHUP
code SIGILL  = prim__SIGILL
code SIGINT  = prim__SIGINT
code SIGQUIT = prim__SIGQUIT
code SIGSEGV = prim__SIGSEGV
code SIGTRAP = prim__SIGTRAP
code SIGUSR1 = prim__SIGUSR1
code SIGUSR2 = prim__SIGUSR2

export %inline
initSignal : Loop => HasIO io => io Signal
initSignal @{MkLoop ptr} = MkSignal <$> primIO (prim__initSignal ptr)

export %inline
startSignal : Signal -> (Signal -> Int64 -> IO ()) -> SigCode -> UVIO ()
startSignal (MkSignal ptr) f c =
  primUV $ prim__startSignal ptr (\p,s => toPrim (f (MkSignal p) s)) (code c)

export %inline
onSignal : Signal -> IO () -> SigCode -> UVIO ()
onSignal s f c = startSignal s (\_,_ => f) c

export %inline
stopSignal : Signal -> UVIO ()
stopSignal (MkSignal ptr) = primUV $ prim__stopSignal ptr

export %inline
freeSignal : HasIO io => Signal -> io ()
freeSignal (MkSignal ptr) = primIO (prim__freeSignal ptr)

export %inline
endSignal : Signal -> UVIO ()
endSignal si = stopSignal si >> freeSignal si

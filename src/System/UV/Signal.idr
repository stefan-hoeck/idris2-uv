module System.UV.Signal

import Derive.Prelude
import System.UV.Loop
import System.UV.Util

%default total
%language ElabReflection

export
data SignalPtr : Type where

public export
record Signal where
  [noHints]
  constructor MkSignal
  signal : Ptr SignalPtr

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
  -> (Ptr SignalPtr -> Int -> PrimIO ())
  -> Int
  -> PrimIO Int

%foreign (idris_uv "uv_signal_stop")
prim__stopSignal : Ptr SignalPtr -> PrimIO Int

%foreign (idris_uv "uv_sigabrt")
prim__SIGABRT : Int

%foreign (idris_uv "uv_sigfpe")
prim__SIGFPE  : Int

%foreign (idris_uv "uv_sighup")
prim__SIGHUP  : Int

%foreign (idris_uv "uv_sigill")
prim__SIGILL  : Int

%foreign (idris_uv "uv_sigint")
prim__SIGINT  : Int

%foreign (idris_uv "uv_sigquit")
prim__SIGQUIT : Int

%foreign (idris_uv "uv_sigsegv")
prim__SIGSEGV : Int

%foreign (idris_uv "uv_sigtrap")
prim__SIGTRAP : Int

%foreign (idris_uv "uv_sigusr1")
prim__SIGUSR1 : Int

%foreign (idris_uv "uv_sigusr2")
prim__SIGUSR2 : Int

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

export
code : SigCode -> Int
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

parameters {auto has : HasIO io}

  export %inline
  initSignal : Loop => io Signal
  initSignal @{MkLoop ptr} = MkSignal <$> primIO (prim__initSignal ptr)

  export %inline
  startSignal : Signal -> (Signal -> Int -> IO ()) -> SigCode -> io Int
  startSignal (MkSignal ptr) f c =
    primIO $ prim__startSignal ptr (\p,s => toPrim (f (MkSignal p) s)) (code c)

  export %inline
  onSignal : Signal -> IO () -> SigCode -> io ()
  onSignal s f c = ignore $ startSignal s (\_,_ => f) c

  export %inline
  stopSignal : Signal -> io Int
  stopSignal (MkSignal ptr) = primIO $ prim__stopSignal ptr

  export %inline
  freeSignal : Signal -> io ()
  freeSignal (MkSignal ptr) = primIO (prim__freeSignal ptr)

  export %inline
  endSignal : Signal -> io ()
  endSignal si = ignore (stopSignal si) >> freeSignal si

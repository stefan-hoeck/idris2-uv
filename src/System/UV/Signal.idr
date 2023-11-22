module System.UV.Signal

import Control.Monad.Either
import Derive.Prelude
import System.UV.Error
import System.UV.Handle
import System.UV.Loop
import System.UV.Util
import System.FFI

%default total
%language ElabReflection

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

%foreign (idris_uv "uv_signal_init")
prim__uv_signal_init : Ptr LoopPtr -> Ptr Signal -> PrimIO Int64

%foreign (idris_uv "uv_signal_start")
prim__uv_signal_start :
     Ptr Signal
  -> (Ptr Signal -> Int64 -> PrimIO ())
  -> Int64
  -> PrimIO Int64

%foreign (idris_uv "uv_signal_stop")
prim__uv_signal_stop : Ptr Signal -> PrimIO Int64

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
signalInit : Loop => Ptr Signal -> UVIO ()
signalInit @{MkLoop ptr} si = primUV (prim__uv_signal_init ptr si)

export %inline
signalStart :
     Ptr Signal
  -> (Ptr Signal -> Int64 -> IO ())
  -> SigCode
  -> UVIO ()
signalStart ptr f c =
  primUV $ prim__uv_signal_start ptr (\p,s => toPrim $ f p s) (code c)

export %inline
signalStop : Ptr Signal -> UVIO ()
signalStop ptr = primUV $ prim__uv_signal_stop ptr

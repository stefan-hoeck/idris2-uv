module System.UV.Signal

import Data.Fuel
import Derive.Prelude
import System.UV.Error
import System.UV.Handle
import System.UV.Loop
import System.UV.Pointer
import System.UV.Resource
import public System.UV.Raw.Signal

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

||| Converts a `SigCode` to the corresponding C constant.
export
code : SigCode -> Int32
code SIGABRT = uv_sigabrt
code SIGFPE  = uv_sigfpe
code SIGHUP  = uv_sighup
code SIGILL  = uv_sigill
code SIGINT  = uv_sigint
code SIGQUIT = uv_sigquit
code SIGSEGV = uv_sigsegv
code SIGTRAP = uv_sigtrap
code SIGUSR1 = uv_sigusr1
code SIGUSR2 = uv_sigusr2

start : Fuel -> IO Bool -> Resource -> Ptr Signal -> Int32 -> UVIO ()

go : Fuel -> IO Bool -> Resource -> Ptr Signal -> Int32 -> IO ()

start f act res h c = uvio $ uv_signal_start h (go f act res) c

go Dry      act res h c = release res
go (More x) act res h c = do
  True     <- act | False => release res
  Right () <- runEitherT $ start x act res h c | Left _ => release res
  pure ()

||| Runs the given `IO` action each time the given signal
||| is received until it either returns `False` or the `Fuel` runs dry.
export
repeatedlyOnSignal : (l : Loop) => Fuel -> SigCode -> IO Bool -> UVIO Resource
repeatedlyOnSignal f c act = do
  h <- mallocPtr Signal
  uvio $ uv_signal_init l.loop h
  res <- manageHandle h
  start f act res h (code c)
  pure res


||| Runs the given `IO` action once when the given signal is received.
export %inline
onSignal : Loop => SigCode -> IO () -> UVIO Resource
onSignal c act = repeatedlyOnSignal (limit 1) c (act $> False)

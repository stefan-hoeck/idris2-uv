module System.UV.Signal

import System.UV.Loop
import System.UV.Pointer
import System.UV.Raw.Handle
import public System.UV.Raw.Signal

%default total

export
Resource (Ptr Signal) where
  release h = uv_close h freePtr

signal_stop : Ptr Signal -> Async [] ()
signal_stop pt =ignore (uv_signal_stop pt) >> release pt

parameters {auto l   : UVLoop}
           {auto has : Has UVError es}
  export
  mkSignal : Async es (Ptr Signal)
  mkSignal = mallocPtr Signal >>= uvAct (uv_signal_init l.loop)

  ||| Reacts on process signals.
  export covering
  onSignal' : SigCode -> (SigCode -> Async es a) -> Async es (Fiber es a)
  onSignal' c run = do
    ps <- mkSignal
    uvOnce run ps signal_stop $ \cb => uv_signal_start ps (\_,_ => cb c) (sigToCode c)

  ||| Reacts on process signals.
  export %inline covering
  onSignal : SigCode -> Async es a -> Async es (Fiber es a)
  onSignal c = onSignal' c . const

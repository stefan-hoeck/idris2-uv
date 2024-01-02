module System.UV.Signal

import System.UV.Async
import System.UV.Error
import System.UV.Resource
import System.UV.Loop
import System.UV.Pointer
import System.UV.Raw.Handle
import public System.UV.Raw.Signal

%default total

export
Resource (Ptr Signal) where
  release h = uv_close h freePtr

parameters {auto l   : UVLoop}
           {auto has : Has UVError es}
  export
  mkSignal : Async es (Cancel, Ptr Signal)
  mkSignal = do
    pt <- mallocPtr Signal >>= uvAct (uv_signal_init l.loop)
    c  <- mkCancel (ignore (uv_signal_stop pt) >> release pt)
    pure (c, pt)

  ||| Reacts on process signals.
  export
  onSignal : SigCode -> (SigCode -> Async [] ()) -> Async es Cancel
  onSignal c run = do
    (r,ps) <- mkSignal
    uvPar1 r run $ \cb => uv_signal_start ps (\_,_ => cb c) (sigToCode c)

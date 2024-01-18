module System.UV.Signal

import System.UV.Loop
import System.UV.Pointer
import System.UV.Raw.Handle
import public System.UV.Raw.Signal

%default total

parameters {auto cc : CloseCB}
  export
  Resource (Ptr Signal) where
    release h = putStrLn "Releasing signal" >> uv_close h cc

parameters {auto l   : UVLoop}
           {auto has : Has UVError es}
  export
  mkSignal : Async es (Ptr Signal)
  mkSignal = mallocPtr Signal >>= uvAct (uv_signal_init l.loop)

  ||| Reacts on process signals.
  |||
  ||| Note: If used in a do-block this will semantically block the
  |||       current fiber.
  |||       Wrap this in `start` to run it in the background.
  export
  onSignal : SigCode -> Async es SigCode
  onSignal c =
    uvCancelableAsync
      mkSignal
      (\cb,p => liftIO $ ignore (uv_signal_stop p) >> cb Canceled)
      release
      (\ps,cb => uv_signal_start ps (\_,_ => cb c) (sigToCode c))

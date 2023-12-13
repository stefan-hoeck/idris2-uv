module System.UV.Signal

import System.Rx
import System.UV.Error
import System.UV.Handle
import System.UV.Loop
import System.UV.Pointer
import public System.UV.Raw.Signal

%default total

||| Repeatedly reacts on process signals.
export
signal : (l : UVLoop) => SigCode -> Source [UVError] SigCode
signal c = MkSource $ do
  h   <- mallocPtr Signal
  ref <- sourceRef [UVError] SigCode (releaseHandle h)
  res <- uv_signal_init l.loop h
  case uvRes res of
    Left e   => error ref e
    Right () => pure ()
  pure $ coldSrc ref $ \cb => do
    res <- uv_signal_start h (\_,_ => cb $ Next [c]) (sigToCode c)
    case uvRes res of
      Left e  => cb (Err $ inject e)
      Right _ => pure ()

module System.UV.Loop

import Data.IORef
import System
import System.UV.Error
import System.UV.Raw.Loop
import System.UV.Raw.Pointer

import public System.UV.Data.RunMode

%default total

public export
record UVLoop where
  [noHints]
  constructor MkLoop
  loop : Ptr Loop

||| Returns the default loop, corresponding to `uv_default_loop`.
export %inline
defaultLoop : HasIO io => io UVLoop
defaultLoop = MkLoop <$> uv_default_loop

||| Sets up the given application by registering it at the default loop
||| and starting the loop afterwards.
covering export
runUV : (UVLoop => IO ()) -> IO ()
runUV act = do
  loop <- defaultLoop
  act @{loop}
  res <- uv_run loop.loop (toCode Default)
  case uvRes {es = [UVError]} res of
    Left (Here err) => die "\{err}"
    Right _         => pure ()

module System.UV.Loop

import Data.IORef
import System
import System.UV.Error
import System.UV.Raw.Loop
import System.UV.Raw.Pointer

import public Control.Monad.Either
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

||| Starts the given loop.
|||
||| For many use-cases, this will literally loop forever or until the
||| application is terminated via an external event, therefore, this is
||| a covering action.
covering export %inline
runLoop : UVLoop -> UVIO ()
runLoop l = uvio $ uv_run l.loop (toCode Default)

||| Sets up the given application by registering it at the default loop
||| and starting the loop afterwards.
covering export
runUV : (UVLoop => IO ()) -> IO ()
runUV act = do
  loop <- defaultLoop
  act @{loop}
  res <- uv_run loop.loop (toCode Default)
  case uvRes res of
    Left err => die "\{err}"
    Right _  => pure ()

export
runUVIO : UVIO () -> IO ()
runUVIO act = do
  Right () <- runEitherT act | Left err => putStrLn "\{err}"
  pure ()

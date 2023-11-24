module System.UV.Loop

import public Control.Monad.Either
import Data.IORef
import System
import System.UV.Error
import System.UV.Util

%default total

export
data LoopPtr : Type where

public export
record Loop where
  [noHints]
  constructor MkLoop
  loop : Ptr LoopPtr

||| A resource that can be safely released, for instance,
||| a pointer whose memory we want to free.
|||
||| Once a resource has been released via `release`,
||| it is safe to dispose of it. Internally, the resource
||| makes sure it can be released only once, so additional
||| calls to `release` just have no effect.
export
record Resource where
  constructor R
  ref : IORef (IO ())

export %inline
unitIO : IO ()
unitIO = pure ()

export
release : Resource -> IO ()
release (R ref) = do
  join (readIORef ref) >> writeIORef ref unitIO

export %inline
handle : HasIO io => IO () -> io (Resource)
handle = map R . newIORef

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_default_loop")
prim__defaultLoop : PrimIO (Ptr LoopPtr)

covering %foreign (idris_uv "uv_run")
prim__loopRun : Ptr LoopPtr -> Bits32 -> PrimIO Int32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Returns the default loop, corresponding to `uv_default_loop`.
export %inline
defaultLoop : HasIO io => io Loop
defaultLoop = MkLoop <$> primIO prim__defaultLoop

||| Starts the given loop.
|||
||| For many use-cases, this will literally loop forever or until the
||| application is terminated via an external event, therefore, this is
||| a covering action.
covering export %inline
runLoop : Loop -> UVIO ()
runLoop l = primUV $ prim__loopRun l.loop 0

||| Sets up the given application by registering it at the default loop
||| and starting the loop afterwards.
covering export
runUV : (Loop => UVIO ()) -> IO ()
runUV act = do
  Right () <- runEitherT run' | Left err => die "\{err}"
  pure ()

  where
    run' : UVIO ()
    run' = do
      loop <- defaultLoop
      act @{loop}
      runLoop loop

export
runUVIO : UVIO () -> IO ()
runUVIO act = do
  Right () <- runEitherT act | Left err => putStrLn "\{err}"
  pure ()

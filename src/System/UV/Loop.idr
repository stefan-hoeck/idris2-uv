module System.UV.Loop

import Control.Monad.Either
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

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_default_loop")
prim__defaultLoop : PrimIO (Ptr LoopPtr)

covering %foreign (idris_uv "uv_run")
prim__loopRun : Ptr LoopPtr -> Bits32 -> PrimIO Int64

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
runLoop (MkLoop ptr) = primUV $ prim__loopRun ptr 0

||| Sets up the given application by registering it at the default loop
||| and starting the loop afterwards.
covering export
runUV : (Loop => UVIO ()) -> UVIO ()
runUV act = do
  loop <- defaultLoop
  act @{loop}
  runLoop loop

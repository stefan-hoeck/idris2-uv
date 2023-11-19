module System.UV.Loop

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

%foreign (idris_uv "uv_run")
prim__loopRun : Ptr LoopPtr -> Bits32 -> PrimIO Int32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

export %inline
defaultLoop : HasIO io => io Loop
defaultLoop = MkLoop <$> primIO prim__defaultLoop

export %inline
runLoop : HasIO io => Loop -> io Int32
runLoop (MkLoop ptr) = primIO $ prim__loopRun ptr 0

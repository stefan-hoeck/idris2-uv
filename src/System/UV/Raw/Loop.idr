module System.UV.Raw.Loop

import System.UV.Raw.Util

%default total

export
data LoopPtr : Type where

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_default_loop")
prim__uv_default_loop : PrimIO (Ptr LoopPtr)

covering %foreign (idris_uv "uv_run")
prim__uv_run : Ptr LoopPtr -> Bits32 -> PrimIO Int32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

export %inline
uv_default_loop : HasIO io => io (Ptr LoopPtr)
uv_default_loop = primIO prim__uv_default_loop

export %inline covering
uv_run : HasIO io => Ptr LoopPtr -> Bits32 -> io Int32
uv_run p b = primIO $ prim__uv_run p b

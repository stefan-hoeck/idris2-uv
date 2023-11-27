module System.UV.Raw.Loop

import System.UV.Raw.Pointer
import System.UV.Raw.Util

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_default_loop")
prim__uv_default_loop : PrimIO (Ptr Loop)

covering %foreign (idris_uv "uv_run")
prim__uv_run : Ptr Loop -> Bits32 -> PrimIO Int32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

export %inline
uv_default_loop : HasIO io => io (Ptr Loop)
uv_default_loop = primIO prim__uv_default_loop

export %inline covering
uv_run : HasIO io => Ptr Loop -> Bits32 -> io Int32
uv_run p b = primIO $ prim__uv_run p b

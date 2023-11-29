module System.UV.Raw.Loop

import System.UV.Raw.Pointer
import System.UV.Raw.Util

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_default_loop")
prim__uv_default_loop : PrimIO (Ptr Loop)

%foreign (idris_uv "uv_loop_init")
prim__uv_loop_init : Ptr Loop -> PrimIO Int32

%foreign (idris_uv "uv_loop_close")
prim__uv_loop_close : Ptr Loop -> PrimIO Int32

%foreign (idris_uv "uv_stop")
prim__uv_stop : Ptr Loop -> PrimIO ()

%foreign (idris_uv "uv_loop_alive")
prim__uv_loop_alive : Ptr Loop -> PrimIO Int32

covering %foreign (idris_uv "uv_run")
prim__uv_run : Ptr Loop -> Bits32 -> PrimIO Int32

export %foreign (idris_uv "uv_run_default")
UV_RUN_DEFAULT : Bits32

export %foreign (idris_uv "uv_run_once")
UV_RUN_ONCE : Bits32

export %foreign (idris_uv "uv_run_nowait")
UV_RUN_NOWAIT : Bits32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

parameters {auto has : HasIO io}

  export %inline
  uv_default_loop : io (Ptr Loop)
  uv_default_loop = primIO prim__uv_default_loop

  export %inline covering
  uv_run : Ptr Loop -> Bits32 -> io Int32
  uv_run p b = primIO $ prim__uv_run p b

  export %inline covering
  uv_loop_init : Ptr Loop -> io Int32
  uv_loop_init p = primIO $ prim__uv_loop_init p

  export %inline
  uv_loop_close : Ptr Loop -> io Int32
  uv_loop_close p = primIO $ prim__uv_loop_close p

  export %inline
  uv_stop : Ptr Loop -> io ()
  uv_stop p = primIO $ prim__uv_stop p

  export %inline
  uv_loop_alive : Ptr Loop -> io Bool
  uv_loop_alive p = int32ToBool <$> primIO (prim__uv_loop_alive p)

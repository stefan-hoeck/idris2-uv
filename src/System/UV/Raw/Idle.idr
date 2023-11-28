module System.UV.Raw.Idle

import System.UV.Raw.Loop
import System.UV.Raw.Pointer
import System.UV.Raw.Util

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_idle_init")
prim__uv_idle_init : Ptr Loop -> Ptr Idle -> PrimIO Int32

%foreign (idris_uv "uv_idle_start")
prim__uv_idle_start : Ptr Idle -> (Ptr Idle -> PrimIO ()) -> PrimIO Int32

%foreign (idris_uv "uv_idle_stop")
prim__uv_idle_stop : Ptr Idle -> PrimIO Int32

%foreign (idris_uv "uv_prepare_init")
prim__uv_prepare_init : Ptr Loop -> Ptr Prepare -> PrimIO Int32

%foreign (idris_uv "uv_prepare_start")
prim__uv_prepare_start : Ptr Prepare -> (Ptr Prepare -> PrimIO ()) -> PrimIO Int32

%foreign (idris_uv "uv_prepare_stop")
prim__uv_prepare_stop : Ptr Prepare -> PrimIO Int32

%foreign (idris_uv "uv_check_init")
prim__uv_check_init : Ptr Loop -> Ptr Check -> PrimIO Int32

%foreign (idris_uv "uv_check_start")
prim__uv_check_start : Ptr Check -> (Ptr Check -> PrimIO ()) -> PrimIO Int32

%foreign (idris_uv "uv_check_stop")
prim__uv_check_stop : Ptr Check -> PrimIO Int32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

parameters {auto has : HasIO io}

  export %inline
  uv_idle_init : Ptr Loop -> Ptr Idle -> io Int32
  uv_idle_init p si = primIO (prim__uv_idle_init p si)

  ||| Start the handle with the given callback, watching for the given idle.
  export %inline
  uv_idle_start : Ptr Idle -> (Ptr Idle -> IO ()) -> io Int32
  uv_idle_start ptr f =
    primIO $ prim__uv_idle_start ptr (\p => toPrim $ f p)

  ||| Stop the handle, the callback will no longer be called.
  export %inline
  uv_idle_stop : Ptr Idle -> io Int32
  uv_idle_stop ptr = primIO $ prim__uv_idle_stop ptr

  export %inline
  uv_prepare_init : Ptr Loop -> Ptr Prepare -> io Int32
  uv_prepare_init p si = primIO (prim__uv_prepare_init p si)

  ||| Start the handle with the given callback, watching for the given prepare.
  export %inline
  uv_prepare_start : Ptr Prepare -> (Ptr Prepare -> IO ()) -> io Int32
  uv_prepare_start ptr f =
    primIO $ prim__uv_prepare_start ptr (\p => toPrim $ f p)

  ||| Stop the handle, the callback will no longer be called.
  export %inline
  uv_prepare_stop : Ptr Prepare -> io Int32
  uv_prepare_stop ptr = primIO $ prim__uv_prepare_stop ptr

  export %inline
  uv_check_init : Ptr Loop -> Ptr Check -> io Int32
  uv_check_init p si = primIO (prim__uv_check_init p si)

  ||| Start the handle with the given callback, watching for the given check.
  export %inline
  uv_check_start : Ptr Check -> (Ptr Check -> IO ()) -> io Int32
  uv_check_start ptr f =
    primIO $ prim__uv_check_start ptr (\p => toPrim $ f p)

  ||| Stop the handle, the callback will no longer be called.
  export %inline
  uv_check_stop : Ptr Check -> io Int32
  uv_check_stop ptr = primIO $ prim__uv_check_stop ptr

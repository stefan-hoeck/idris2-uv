module System.UV.Raw.Idle

import System.UV.Raw.Callback
import System.UV.Raw.Handle
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
prim__uv_idle_start : Ptr Idle -> AnyPtr -> PrimIO Int32

%foreign (idris_uv "uv_idle_stop")
prim__uv_idle_stop : Ptr Idle -> PrimIO Int32

%foreign (idris_uv "uv_prepare_init")
prim__uv_prepare_init : Ptr Loop -> Ptr Prepare -> PrimIO Int32

%foreign (idris_uv "uv_prepare_start")
prim__uv_prepare_start : Ptr Prepare -> AnyPtr -> PrimIO Int32

%foreign (idris_uv "uv_prepare_stop")
prim__uv_prepare_stop : Ptr Prepare -> PrimIO Int32

%foreign (idris_uv "uv_check_init")
prim__uv_check_init : Ptr Loop -> Ptr Check -> PrimIO Int32

%foreign (idris_uv "uv_check_start")
prim__uv_check_start : Ptr Check -> AnyPtr -> PrimIO Int32

%foreign (idris_uv "uv_check_stop")
prim__uv_check_stop : Ptr Check -> PrimIO Int32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

parameters {auto has : HasIO io}

  export %inline
  uv_idle_stop : Ptr Idle -> io Int32
  uv_idle_stop h = primIO $ prim__uv_idle_stop h

  export %inline
  uv_idle_init : Ptr Loop -> Ptr Idle -> io Int32
  uv_idle_init l h = primIO $ prim__uv_idle_init l h

  export
  uv_idle_start : Ptr Idle -> (Ptr Idle -> IO ()) -> io Int32
  uv_idle_start p f = do
    cb <- ptrCB f
    uv_handle_set_data p cb
    primIO $ prim__uv_idle_start p cb

  export %inline
  uv_check_stop : Ptr Check -> io Int32
  uv_check_stop h = primIO $ prim__uv_check_stop h

  export %inline
  uv_check_init : Ptr Loop -> Ptr Check -> io Int32
  uv_check_init l h = primIO $ prim__uv_check_init l h

  export
  uv_check_start : Ptr Check -> (Ptr Check -> IO ()) -> io Int32
  uv_check_start p f = do
    cb <- ptrCB f
    uv_handle_set_data p cb
    primIO $ prim__uv_check_start p cb

  export %inline
  uv_prepare_stop : Ptr Prepare -> io Int32
  uv_prepare_stop h = primIO $ prim__uv_prepare_stop h

  export %inline
  uv_prepare_init : Ptr Loop -> Ptr Prepare -> io Int32
  uv_prepare_init l h = primIO $ prim__uv_prepare_init l h

  export
  uv_prepare_start : Ptr Prepare -> (Ptr Prepare -> IO ()) -> io Int32
  uv_prepare_start p f = do
    cb <- ptrCB f
    uv_handle_set_data p cb
    primIO $ prim__uv_prepare_start p cb

module System.UV.Raw.Signal

import System.UV.Raw.Callback
import System.UV.Raw.Handle
import System.UV.Raw.Loop
import System.UV.Raw.Pointer
import System.UV.Raw.Util

import public System.UV.Data.Signal

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_signal_init")
prim__uv_signal_init : Ptr Loop -> Ptr Signal -> PrimIO Int32

%foreign (idris_uv "uv_signal_start")
prim__uv_signal_start : Ptr Signal -> AnyPtr -> Bits32 -> PrimIO Int32

%foreign (idris_uv "uv_signal_stop")
prim__uv_signal_stop : Ptr Signal -> PrimIO Int32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

parameters {auto has : HasIO io}

  ||| Stops the given signal.
  export
  uv_signal_stop : Ptr Signal -> io Int32
  uv_signal_stop h = primIO $ prim__uv_signal_stop h

  export %inline
  uv_signal_init : Ptr Loop -> Ptr Signal -> io Int32
  uv_signal_init l h = primIO $ prim__uv_signal_init l h

  ||| Start the handle with the given callback, watching for the given signal.
  export
  uv_signal_start :
       Ptr Signal
    -> (Ptr Signal -> Bits32 -> IO ())
    -> Bits32
    -> io Int32
  uv_signal_start h f c = do
    cb <- ptrUintCB f
    uv_handle_set_data h cb
    primIO $ prim__uv_signal_start h cb c

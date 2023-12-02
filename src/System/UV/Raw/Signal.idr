module System.UV.Raw.Signal

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
prim__uv_signal_start :
     Ptr Signal
  -> (Ptr Signal -> Bits32 -> PrimIO ())
  -> Bits32
  -> PrimIO Int32

%foreign (idris_uv "uv_signal_stop")
prim__uv_signal_stop : Ptr Signal -> PrimIO Int32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

parameters {auto has : HasIO io}

  export %inline
  uv_signal_init : Ptr Loop -> Ptr Signal -> io Int32
  uv_signal_init p si = primIO (prim__uv_signal_init p si)

  ||| Start the handle with the given callback, watching for the given signal.
  export %inline
  uv_signal_start :
       Ptr Signal
    -> (Ptr Signal -> Bits32 -> IO ())
    -> Bits32
    -> io Int32
  uv_signal_start ptr f c =
    primIO $ prim__uv_signal_start ptr (\p,s => toPrim $ f p s) c

  ||| Stop the handle, the callback will no longer be called.
  export %inline
  uv_signal_stop : Ptr Signal -> io Int32
  uv_signal_stop ptr = primIO $ prim__uv_signal_stop ptr

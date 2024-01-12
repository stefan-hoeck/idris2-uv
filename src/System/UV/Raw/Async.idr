module System.UV.Raw.Async

import System.UV.Raw.Callback
import System.UV.Raw.Handle
import System.UV.Raw.Loop
import System.UV.Raw.Pointer
import System.UV.Raw.Util

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_async_init")
prim__uv_async_init : Ptr Loop -> Ptr Async -> AnyPtr -> PrimIO Int32

%foreign (idris_uv "uv_async_send")
prim__uv_async_send : Ptr Async -> PrimIO Int32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

parameters {auto has : HasIO io}
  export
  uv_async_init : Ptr Loop -> Ptr Async -> (Ptr Async -> IO ()) -> io Int32
  uv_async_init l h f = do
    cb <- ptrCB f
    uv_handle_set_data h cb
    primIO $ prim__uv_async_init l h cb

  export %inline
  uv_async_send : Ptr Async -> io Int32
  uv_async_send p = primIO $ prim__uv_async_send p

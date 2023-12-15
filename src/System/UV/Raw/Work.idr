module System.UV.Raw.Work

import System.UV.Raw.Loop
import System.UV.Raw.Pointer
import System.UV.Raw.Util

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_async_init_and_send")
prim__uv_async_init_and_send :
     Ptr Loop
  -> Ptr Async
  -> (Ptr Async -> PrimIO ())
  -> PrimIO ()


--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

export %inline
uv_async_init_and_send :
    {auto has : HasIO io}
  -> Ptr Loop
  -> Ptr Async
  -> (Ptr Async -> IO ())
  -> io ()
uv_async_init_and_send l w cb =
  primIO $ prim__uv_async_init_and_send l w (\x => toPrim $ cb x)

module System.UV.Work

import System.UV.Loop
import System.UV.Pointer
import System.UV.Raw.Util

%default total

%foreign (idris_uv "uv_async_init")
prim__uv_async_init :
     Ptr Loop
  -> Ptr Async
  -> (Ptr Async -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_async_send")
prim__uv_async_send : Ptr Async -> PrimIO Int32

export %inline
uv_async_init : Ptr Loop -> Ptr Async -> (Ptr Async -> IO ()) -> IO Int32
uv_async_init pl pa cb =
  primIO $ prim__uv_async_init pl pa (\p => toPrim $ cb p)

export %inline
uv_async_send : Ptr Async -> IO Int32
uv_async_send pa = primIO $ prim__uv_async_send pa


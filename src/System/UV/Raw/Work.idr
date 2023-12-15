module System.UV.Raw.Work

import System.UV.Raw.Loop
import System.UV.Raw.Pointer
import System.UV.Raw.Util

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_queue_work")
prim__uv_queue_work :
     Ptr Loop
  -> Ptr Work
  -> (Ptr Work -> PrimIO ())
  -> (Ptr Work -> Int32 -> PrimIO ())
  -> PrimIO Int32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Initializes a work request which will run the given work_cb in a
||| thread from the threadpool. Once work_cb is completed, after_work_cb will
||| be called on the loop thread.
|||
||| This request can be cancelled with uv_cancel().
export %inline
uv_queue_work :
    {auto has : HasIO io}
  -> Ptr Loop
  -> Ptr Work
  -> (Ptr Work -> IO ())
  -> (Ptr Work -> Int32 -> IO ())
  -> io Int32
uv_queue_work l w cb acb =
  primIO $ prim__uv_queue_work l w (\x => toPrim $ cb x) (\x,y => toPrim $ acb x y)

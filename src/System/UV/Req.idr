module System.UV.Req

import System.FFI
import System.UV.Handle
import System.UV.Pointer
import System.UV.Loop
import System.UV.Util

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_req_size")
prim__uv_req_size : Int -> Int

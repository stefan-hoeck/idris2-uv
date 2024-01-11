module System.UV.Raw.Req

import System.UV.Raw.Loop
import System.UV.Raw.Pointer
import System.UV.Raw.Util

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_cancel")
prim__uv_cancel : Ptr Req -> PrimIO Int32

%foreign (idris_uv "uv_req_get_data")
prim__uv_req_get_data : Ptr Req -> PrimIO AnyPtr

%foreign (idris_uv "uv_req_set_data")
prim__uv_req_set_data : Ptr Req -> AnyPtr -> PrimIO ()

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

parameters {auto has : HasIO io}
           {auto 0 prf : PCast t Req}

  export %inline
  uv_cancel : Ptr t -> io Int32
  uv_cancel req = primIO $ prim__uv_cancel (castPtr req)

  ||| Returns the data associated with a request.
  export %inline
  uv_req_get_data : Ptr t -> io AnyPtr
  uv_req_get_data req = primIO $ prim__uv_req_get_data (castPtr req)

  ||| Sets the data associated with a request.
  export %inline
  uv_req_set_data : Ptr t -> AnyPtr -> io ()
  uv_req_set_data req dat = primIO $ prim__uv_req_set_data (castPtr req) dat

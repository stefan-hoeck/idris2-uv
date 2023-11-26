module System.UV.Raw.Handle

import System.UV.Raw.Loop
import System.UV.Raw.Pointer
import System.UV.Raw.Util

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_is_active")
prim__uv_is_active : Ptr Handle -> PrimIO Int32

%foreign (idris_uv "uv_is_closing")
prim__uv_is_closing : Ptr Handle -> PrimIO Int32

%foreign (idris_uv "uv_close")
prim__uv_close : Ptr Handle -> (Ptr Handle -> PrimIO ()) -> PrimIO ()

%foreign (idris_uv "uv_ref")
prim__uv_ref : Ptr Handle -> PrimIO ()

%foreign (idris_uv "uv_unref")
prim__uv_unref : Ptr Handle -> PrimIO ()

%foreign (idris_uv "uv_has_ref")
prim__uv_has_ref : Ptr Handle -> PrimIO Int

%foreign (idris_uv "uv_handle_get_data")
prim__uv_handle_get_data : Ptr Handle -> PrimIO AnyPtr

%foreign (idris_uv "uv_handle_set_data")
prim__uv_handle_set_data : Ptr Handle -> AnyPtr -> PrimIO ()

%foreign (idris_uv "uv_handle_type")
prim__uv_handle_type : Ptr Handle -> PrimIO Int

||| Returns the name of the handle type.
export %foreign (idris_uv "uv_handle_type_name")
uv_handle_type_name : Int -> String

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

parameters {auto has   : HasIO io}
           {auto 0 prf : PCast t Handle}

  export %inline
  uv_is_active : Ptr t -> io Int32
  uv_is_active p = primIO (prim__uv_is_active $ castPtr p)

  export %inline
  uv_is_closing : Ptr t -> io Int32
  uv_is_closing p = primIO (prim__uv_is_closing $ castPtr p)

  ||| Request a handle to be closed.
  |||
  ||| This *must* be called before releasing the handle from memory,
  ||| which can be done from within the callback or after the callback
  ||| has returned.
  export
  uv_close : Ptr t -> (Ptr Handle -> IO ()) -> io ()
  uv_close p f = primIO $ prim__uv_close (castPtr p) (\h => toPrim $ f h)

  ||| Reference a handle.
  |||
  ||| This is an idempotent action, so calling it several times has no
  ||| additional effect.
  export %inline
  uv_ref : Ptr t -> io ()
  uv_ref p = primIO $ prim__uv_ref (castPtr p)

  ||| Un-reference a handle.
  |||
  ||| This is an idempotent action, so calling it several times has no
  ||| additional effect.
  export %inline
  uv_unref : Ptr t -> io ()
  uv_unref p = primIO $ prim__uv_unref (castPtr p)

  ||| Returns `True` is the handle is currently referenced.
  export %inline
  uv_has_ref : Ptr t -> io Bool
  uv_has_ref p = intToBool <$> primIO (prim__uv_has_ref $ castPtr p)

  ||| Returns a pointer to the data associated with a handle.
  export %inline
  uv_handle_get_data : Ptr t -> io AnyPtr
  uv_handle_get_data p = primIO $ prim__uv_handle_get_data (castPtr p)

  ||| Sets the data associated with a handle
  export %inline
  uv_handle_set_data : Ptr t -> AnyPtr -> io ()
  uv_handle_set_data p ap = primIO $ prim__uv_handle_set_data (castPtr p) ap

  ||| Returns the type the current handle.
  export %inline
  uv_handle_type : Ptr t -> io Int
  uv_handle_type p = primIO $ prim__uv_handle_type (castPtr p)

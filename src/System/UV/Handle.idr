module System.UV.Handle

import System.FFI
import System.UV.Loop
import System.UV.Pointer
import System.UV.Util

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_is_active")
prim__uv_is_active : Ptr Handle -> PrimIO Int

%foreign (idris_uv "uv_is_closing")
prim__uv_is_closing : Ptr Handle -> PrimIO Int

%foreign (idris_uv "uv_close")
prim__uv_close : Ptr Handle -> (Ptr Handle -> PrimIO ()) -> PrimIO ()

%foreign (idris_uv "uv_ref")
prim__uv_ref : Ptr Handle -> PrimIO ()

%foreign (idris_uv "uv_unref")
prim__uv_unref : Ptr Handle -> PrimIO ()

%foreign (idris_uv "uv_has_ref")
prim__uv_has_ref : Ptr Handle -> PrimIO Int

%foreign (idris_uv "uv_handle_size")
prim__uv_handle_size : Int -> Int

%foreign (idris_uv "uv_handle_get_data")
prim__uv_handle_get_data : Ptr Handle -> PrimIO AnyPtr

%foreign (idris_uv "uv_handle_set_data")
prim__uv_handle_set_data : Ptr Handle -> AnyPtr -> PrimIO ()

%foreign (idris_uv "uv_handle_type")
prim__uv_handle_type : Ptr Handle -> PrimIO Int

%foreign (idris_uv "uv_handle_type_name")
prim__uv_handle_type_name : Int -> String

--------------------------------------------------------------------------------
-- Safe Casts
--------------------------------------------------------------------------------

parameters {auto has   : HasIO io}
           {auto 0 prf : PCast t Handle}

  export %inline
  isActive : Ptr t -> io Bool
  isActive p = intToBool <$> primIO (prim__uv_is_active $ castPtr p)

  export %inline
  isClosing : Ptr t -> io Bool
  isClosing p = intToBool <$> primIO (prim__uv_is_closing $ castPtr p)

  ||| Request a handle to be closed.
  |||
  ||| This *must* be called before releasing the handle from memore,
  ||| which can be done from within the callback or after the callback
  ||| has returned.
  export
  close : Ptr t -> (Ptr Handle -> IO ()) -> io ()
  close p f = primIO $ prim__uv_close (castPtr p) (\h => toPrim $ f h)

  ||| Reference a handle.
  |||
  ||| This is an idempotent action, so calling it several times has no
  ||| additional effect.
  export %inline
  ref : Ptr t -> io ()
  ref p = primIO $ prim__uv_ref (castPtr p)

  ||| Un-reference a handle.
  |||
  ||| This is an idempotent action, so calling it several times has no
  ||| additional effect.
  export %inline
  unref : Ptr t -> io ()
  unref p = primIO $ prim__uv_unref (castPtr p)

  ||| Returns `True` is the handle is currently referenced.
  export %inline
  hasRef : Ptr t -> io Bool
  hasRef p = intToBool <$> primIO (prim__uv_has_ref $ castPtr p)

  ||| Returns a pointer to the data associated with a handle.
  export %inline
  getData : Ptr t -> io AnyPtr
  getData p = primIO $ prim__uv_handle_get_data (castPtr p)

  ||| Sets the data associated with a handle
  export %inline
  setData : Ptr t -> AnyPtr -> io ()
  setData p ap = primIO $ prim__uv_handle_set_data (castPtr p) ap

  ||| Returns the type the current handle.
  export %inline
  handleType : Ptr t -> io Int
  handleType p = primIO $ prim__uv_handle_type (castPtr p)


||| Returns the name of the handle type.
export %inline
handleTypeName : Int -> String
handleTypeName = prim__uv_handle_type_name

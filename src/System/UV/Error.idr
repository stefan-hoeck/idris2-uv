module System.UV.Error

import public Control.Monad.Either
import Derive.Prelude
import System.UV.Util

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_strerror")
prim__uv_strerror : Int32 -> String

%foreign (idris_uv "uv_err_name")
prim__uv_err_name : Int32 -> String

export %foreign (idris_uv "uv_EOF")
UV_EOF : Int32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Core error type for working with this library.
public export
record UVError where
  constructor MkUVError
  code : Int32
  name : String
  msg  : String

export
fromCode : Int32 -> UVError
fromCode n = MkUVError n (prim__uv_err_name n) (prim__uv_strerror n)

%runElab derive "UVError" [Show,Eq]

export
Interpolation UVError where
  interpolate err = "\{err.msg} (code \{show err.code})"

public export
0 UVIO : Type -> Type
UVIO = EitherT UVError IO

export
uvRes : Int32 -> Either UVError ()
uvRes n = if n < 0 then Left $ fromCode n else Right ()

export %inline
toErr : Int32 -> Maybe UVError
toErr = either Just (const Nothing) . uvRes

export %inline
checkStatus : Int32 -> UVIO ()
checkStatus = MkEitherT . pure . uvRes

export %inline
uvio : IO Int32 -> UVIO ()
uvio io = MkEitherT $ uvRes <$> io

export
primUV : PrimIO Int32 -> UVIO ()
primUV io = MkEitherT $ uvRes <$> primIO io

module System.UV.Error

import Control.Monad.Either
import Derive.Prelude
import System.UV.Util

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_strerror")
prim__uv_strerror : Int64 -> String

%foreign (idris_uv "uv_err_name")
prim__uv_err_name : Int64 -> String

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Core error type for working with this library.
public export
record UVError where
  constructor MkUVError
  code : Int64
  name : String
  msg  : String

export
fromCode : Int64 -> UVError
fromCode n = MkUVError n (prim__uv_err_name n) (prim__uv_strerror n)

%runElab derive "UVError" [Show,Eq]

export
Interpolation UVError where
  interpolate err = "\{err.msg} (code \{show err.code})"

public export
0 UVIO : Type -> Type
UVIO = EitherT UVError IO

export
uvRes : Int64 -> Either UVError ()
uvRes n = if n < 0 then Left $ fromCode n else Right ()

export
primUV : PrimIO Int64 -> UVIO ()
primUV io = MkEitherT $ uvRes <$> primIO io

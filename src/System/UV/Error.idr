module System.UV.Error

import System.UV.Pointer
import System.UV.Util

import public Control.Monad.Either
import public System.UV.Data.Error

%default total

public export
0 UVIO : Type -> Type
UVIO = EitherT UVError IO

export
uvRes : Int32 -> Either UVError ()
uvRes n = if n < 0 then Left $ fromCode n else Right ()

export %inline
checkStatus : Int32 -> UVIO ()
checkStatus = MkEitherT . pure . uvRes

export %inline
uvio : IO Int32 -> UVIO ()
uvio io = MkEitherT $ uvRes <$> io

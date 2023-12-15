module System.UV.Error

import System.UV.Pointer
import System.UV.Util

import public System.UV.Data.Error

%default total

export
uvRes : Int32 -> Either UVError ()
uvRes n = if n < 0 then Left $ fromCode n else Right ()

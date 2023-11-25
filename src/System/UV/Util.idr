module System.UV.Util

import Data.IORef

%default total

public export
idris_uv : String -> String
idris_uv fn = "C:" ++ fn ++ ",libuv-idris"

export %inline
boolToInt32 : Bool -> Int32
boolToInt32 False = 0
boolToInt32 True  = 1

export %inline
int32ToBool : Int32 -> Bool
int32ToBool 0 = False
int32ToBool _ = True

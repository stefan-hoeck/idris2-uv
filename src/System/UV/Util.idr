module System.UV.Util

import Data.IORef

%default total

public export
idris_uv : String -> String
idris_uv fn = "C:" ++ fn ++ ",libuv-idris"

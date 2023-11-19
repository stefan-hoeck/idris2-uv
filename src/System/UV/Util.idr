module System.UV.Util

%default total

public export
idris_uv : String -> String
idris_uv fn = "C:" ++ fn ++ ",libuv-idris"

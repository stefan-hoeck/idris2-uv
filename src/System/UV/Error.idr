module System.UV.Error

import System.UV.Pointer
import System.UV.Util

import public IO.Async
import public System.UV.Data.Error

%default total

--------------------------------------------------------------------------------
-- UV interop
--------------------------------------------------------------------------------

parameters {auto has : Has UVError es}

  export
  uvCheck : a -> Int32 -> Result es a
  uvCheck v n = if n < 0 then Left (inject $ fromCode n) else Right v

  export %inline
  uvRes : Int32 -> Result es ()
  uvRes = uvCheck ()

  export
  uv : IO Int32 -> Async es ()
  uv = liftEither . map uvRes

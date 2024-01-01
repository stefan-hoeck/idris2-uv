module System.UV.Error

import System.UV.Pointer
import System.UV.Util

import public Data.List.Quantifiers.Extra
import public System.UV.Data.Error

%default total

public export
0 Outcome : List Type -> Type -> Type
Outcome es a = Either (HSum es) a

export
uvCheck : Has UVError es => a -> Int32 -> Outcome es a
uvCheck v n = if n < 0 then Left (inject $ fromCode n) else Right v

export %inline
uvRes : Has UVError es => Int32 -> Outcome es ()
uvRes = uvCheck ()

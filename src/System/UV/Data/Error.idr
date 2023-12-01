module System.UV.Data.Error

import Derive.Prelude

%language ElabReflection
%default total

public export
data UVError : Type where
  EOF : UVError

%runElab derive "UVError" [Show,Eq]

export
toCode : UVError -> Int32

export
fromCode : Int32 -> UVError

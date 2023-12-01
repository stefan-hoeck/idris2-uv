module System.UV.Data.RunMode

import Derive.Prelude

%language ElabReflection
%default total

public export
data RunMode : Type where
  Default : RunMode
  Once    : RunMode
  NoWait  : RunMode

%runElab derive "RunMode" [Show,Eq]

export
toCode : RunMode -> Bits32
toCode Default = 0
toCode Once = 1
toCode NoWait = 2
toCode Default = 0
toCode Once = 1
toCode NoWait = 2

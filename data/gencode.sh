#!/usr/bin/env bash

make -C codegen all
codegen/error_gen > src/System/UV/Data/Error.idr

cat > src/System/UV/Data/RunMode.idr << EOT
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
EOT

codegen/run_mode_gen >> src/System/UV/Data/RunMode.idr

cat > src/System/UV/Data/Pointer.idr << EOT
module System.UV.Data.Pointer

%default total
EOT

codegen/size_gen >> src/System/UV/Data/Pointer.idr

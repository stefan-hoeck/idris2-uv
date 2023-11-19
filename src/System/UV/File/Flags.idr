module System.UV.File.Flags

import Derive.Prelude
import System.UV.Util

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_rdonly")
prim__RDONLY : Bits32

%foreign (idris_uv "uv_wronly")
prim__WRONLY : Bits32

%foreign (idris_uv "uv_rdwr")
prim__RDWR : Bits32

%foreign (idris_uv "uv_append")
prim__APPEND : Bits32

%foreign (idris_uv "uv_creat")
prim__CREAT : Bits32

%foreign (idris_uv "uv_S_IRWXU")
prim__S_IRWXU : Bits32

%foreign (idris_uv "uv_S_IRUSR")
prim__S_IRUSR : Bits32

%foreign (idris_uv "uv_S_IWUSR")
prim__S_IWUSR : Bits32

%foreign (idris_uv "uv_S_IXUSR")
prim__S_IXUSR : Bits32

%foreign (idris_uv "uv_S_IRWXG")
prim__S_IRWXG : Bits32

%foreign (idris_uv "uv_S_IRGRP")
prim__S_IRGRP : Bits32

%foreign (idris_uv "uv_S_IWGRP")
prim__S_IWGRP : Bits32

%foreign (idris_uv "uv_S_IXGRP")
prim__S_IXGRP : Bits32

%foreign (idris_uv "uv_S_IRWXO")
prim__S_IRWXO : Bits32

%foreign (idris_uv "uv_S_IROTH")
prim__S_IROTH : Bits32

%foreign (idris_uv "uv_S_IWOTH")
prim__S_IWOTH : Bits32

%foreign (idris_uv "uv_S_IXOTH")
prim__S_IXOTH : Bits32

--------------------------------------------------------------------------------
-- Flags
--------------------------------------------------------------------------------

public export
record Flags where
  constructor MkFlags
  flags : Bits32

%runElab derive "Flags" [Show,Eq,Ord]

export %inline
Semigroup Flags where
  MkFlags x <+> MkFlags y = MkFlags $ prim__or_Bits32 x y

export %inline
Monoid Flags where
  neutral = MkFlags 0

export %inline
RDONLY : Flags
RDONLY = MkFlags prim__RDONLY

export %inline
WRONLY : Flags
WRONLY = MkFlags prim__WRONLY

export %inline
RDWR : Flags
RDWR = MkFlags prim__RDWR

export %inline
APPEND : Flags
APPEND = MkFlags prim__APPEND

export %inline
CREAT : Flags
CREAT = MkFlags prim__CREAT


--------------------------------------------------------------------------------
-- Mode
--------------------------------------------------------------------------------

public export
record Mode where
  constructor MkMode
  mode : Bits32

%runElab derive "Flags.Mode" [Show,Eq,Ord]

export %inline
Semigroup Flags.Mode where
  MkMode x <+> MkMode y = MkMode $ prim__or_Bits32 x y

export %inline
Monoid Flags.Mode where
  neutral = MkMode 0

export %inline
S_IRWXU : Flags.Mode
S_IRWXU = MkMode prim__S_IRWXU

export %inline
S_IRUSR : Flags.Mode
S_IRUSR = MkMode prim__S_IRUSR

export %inline
S_IWUSR : Flags.Mode
S_IWUSR = MkMode prim__S_IWUSR

export %inline
S_IXUSR : Flags.Mode
S_IXUSR = MkMode prim__S_IXUSR

export %inline
S_IRWXG : Flags.Mode
S_IRWXG = MkMode prim__S_IRWXG

export %inline
S_IRGRP : Flags.Mode
S_IRGRP = MkMode prim__S_IRGRP

export %inline
S_IWGRP : Flags.Mode
S_IWGRP = MkMode prim__S_IWGRP

export %inline
S_IXGRP : Flags.Mode
S_IXGRP = MkMode prim__S_IXGRP

export %inline
S_IRWXO : Flags.Mode
S_IRWXO = MkMode prim__S_IRWXO

export %inline
S_IROTH : Flags.Mode
S_IROTH = MkMode prim__S_IROTH

export %inline
S_IWOTH : Flags.Mode
S_IWOTH = MkMode prim__S_IWOTH

export %inline
S_IXOTH : Flags.Mode
S_IXOTH = MkMode prim__S_IXOTH

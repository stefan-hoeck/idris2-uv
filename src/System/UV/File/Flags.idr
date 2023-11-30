module System.UV.File.Flags

import Derive.Prelude
import System.UV.Util

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

export %foreign (idris_uv "uv_rdonly")
uv_rdonly : Bits32

export %foreign (idris_uv "uv_wronly")
uv_wronly : Bits32

export %foreign (idris_uv "uv_rdwr")
uv_rdwr : Bits32

export %foreign (idris_uv "uv_append")
uv_append : Bits32

export %foreign (idris_uv "uv_creat")
uv_creat : Bits32

export %foreign (idris_uv "uv_s_irwxu")
uv_s_irwxu : Bits32

export %foreign (idris_uv "uv_s_irusr")
uv_s_irusr : Bits32

export %foreign (idris_uv "uv_s_iwusr")
uv_s_iwusr : Bits32

export %foreign (idris_uv "uv_s_ixusr")
uv_s_ixusr : Bits32

export %foreign (idris_uv "uv_s_irwxg")
uv_s_irwxg : Bits32

export %foreign (idris_uv "uv_s_irgrp")
uv_s_irgrp : Bits32

export %foreign (idris_uv "uv_s_iwgrp")
uv_s_iwgrp : Bits32

export %foreign (idris_uv "uv_s_ixgrp")
uv_s_ixgrp : Bits32

export %foreign (idris_uv "uv_s_irwxo")
uv_s_irwxo : Bits32

export %foreign (idris_uv "uv_s_iroth")
uv_s_iroth : Bits32

export %foreign (idris_uv "uv_s_iwoth")
uv_s_iwoth : Bits32

export %foreign (idris_uv "uv_s_ixoth")
uv_s_ixoth : Bits32

--------------------------------------------------------------------------------
-- Flags
--------------------------------------------------------------------------------

public export
record Flags where
  constructor MkFlags
  flags : Bits32

%runElab derive "Flags" [Show,Eq,Ord,Num]

export %inline
Semigroup Flags where
  MkFlags x <+> MkFlags y = MkFlags $ prim__or_Bits32 x y

export %inline
Monoid Flags where
  neutral = MkFlags 0

export %inline
RDONLY : Flags
RDONLY = MkFlags uv_rdonly

export %inline
WRONLY : Flags
WRONLY = MkFlags uv_wronly

export %inline
RDWR : Flags
RDWR = MkFlags uv_rdwr

export %inline
APPEND : Flags
APPEND = MkFlags uv_append

export %inline
CREAT : Flags
CREAT = MkFlags uv_creat


--------------------------------------------------------------------------------
-- Mode
--------------------------------------------------------------------------------

public export
record Mode where
  constructor MkMode
  mode : Bits32

%runElab derive "Flags.Mode" [Show,Eq,Ord,Num]

export %inline
Semigroup Flags.Mode where
  MkMode x <+> MkMode y = MkMode $ prim__or_Bits32 x y

export %inline
Monoid Flags.Mode where
  neutral = MkMode 0

export %inline
S_IRWXU : Flags.Mode
S_IRWXU = MkMode uv_s_irwxu

export %inline
S_IRUSR : Flags.Mode
S_IRUSR = MkMode uv_s_irusr

export %inline
S_IWUSR : Flags.Mode
S_IWUSR = MkMode uv_s_iwusr

export %inline
S_IXUSR : Flags.Mode
S_IXUSR = MkMode uv_s_ixusr

export %inline
S_IRWXG : Flags.Mode
S_IRWXG = MkMode uv_s_irwxg

export %inline
S_IRGRP : Flags.Mode
S_IRGRP = MkMode uv_s_irgrp

export %inline
S_IWGRP : Flags.Mode
S_IWGRP = MkMode uv_s_iwgrp

export %inline
S_IXGRP : Flags.Mode
S_IXGRP = MkMode uv_s_ixgrp

export %inline
S_IRWXO : Flags.Mode
S_IRWXO = MkMode uv_s_irwxo

export %inline
S_IROTH : Flags.Mode
S_IROTH = MkMode uv_s_iroth

export %inline
S_IWOTH : Flags.Mode
S_IWOTH = MkMode uv_s_iwoth

export %inline
S_IXOTH : Flags.Mode
S_IXOTH = MkMode uv_s_ixoth

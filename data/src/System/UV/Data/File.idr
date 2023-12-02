module System.UV.Data.File

import Derive.Prelude

%language ElabReflection
%default total

public export
data DirentType : Type where
  DirentUnknown : DirentType
  DirentFile    : DirentType
  DirentDir     : DirentType
  DirentLink    : DirentType
  DirentFifo    : DirentType
  DirentSocket  : DirentType
  DirentChar    : DirentType
  DirentBlock   : DirentType

%runElab derive "DirentType" [Show,Eq]

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

public export
record Mode where
  constructor MkMode
  mode : Bits32

%runElab derive "File.Mode" [Show,Eq,Ord,Num]

export %inline
Semigroup File.Mode where
  MkMode x <+> MkMode y = MkMode $ prim__or_Bits32 x y

export %inline
Monoid File.Mode where
  neutral = MkMode 0

public export
direntCode : DirentType -> Bits32
direntCode DirentUnknown = 0
direntCode DirentFile    = 1
direntCode DirentDir     = 2
direntCode DirentLink    = 3
direntCode DirentFifo    = 4
direntCode DirentSocket  = 5
direntCode DirentChar    = 6
direntCode DirentBlock   = 7

public export
direntFromCode : Bits32 -> DirentType
direntFromCode 1 = DirentFile
direntFromCode 2 = DirentDir
direntFromCode 3 = DirentLink
direntFromCode 4 = DirentFifo
direntFromCode 5 = DirentSocket
direntFromCode 6 = DirentChar
direntFromCode 7 = DirentBlock
direntFromCode _ = DirentUnknown

export %inline
APPEND : Flags
APPEND = 1024

export %inline
CREAT : Flags
CREAT = 64

export %inline
DIRECT : Flags
DIRECT = 16384

export %inline
DIRECTORY : Flags
DIRECTORY = 65536

export %inline
NOATIME : Flags
NOATIME = 0

export %inline
NOCTTY : Flags
NOCTTY = 256

export %inline
NOFOLLOW : Flags
NOFOLLOW = 131072

export %inline
NONBLOCK : Flags
NONBLOCK = 2048

export %inline
RANDOM : Flags
RANDOM = 0

export %inline
RDONLY : Flags
RDONLY = 0

export %inline
RDWR : Flags
RDWR = 2

export %inline
SEQUENTIAL : Flags
SEQUENTIAL = 0

export %inline
SHORT_LIVED : Flags
SHORT_LIVED = 0

export %inline
SYMLINK : Flags
SYMLINK = 0

export %inline
SYNC : Flags
SYNC = 1052672

export %inline
TEMPORARY : Flags
TEMPORARY = 0

export %inline
TRUNC : Flags
TRUNC = 512

export %inline
WRONLY : Flags
WRONLY = 1

export %inline
RWXU : File.Mode
RWXU = 448

export %inline
RUSR : File.Mode
RUSR = 256

export %inline
WUSR : File.Mode
WUSR = 128

export %inline
XUSR : File.Mode
XUSR = 64

export %inline
RWXG : File.Mode
RWXG = 56

export %inline
RGRP : File.Mode
RGRP = 32

export %inline
WGRP : File.Mode
WGRP = 16

export %inline
XGRP : File.Mode
XGRP = 8

export %inline
RWXO : File.Mode
RWXO = 7

export %inline
ROTH : File.Mode
ROTH = 4

export %inline
WOTH : File.Mode
WOTH = 2

export %inline
XOTH : File.Mode
XOTH = 1

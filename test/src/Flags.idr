module Flags

import System.UV.File.Flags
import Hedgehog

%default total

prop_RDONLY : Property
prop_RDONLY = property1 $ RDONLY === MkFlags 0

prop_WRONLY : Property
prop_WRONLY = property1 $ WRONLY === MkFlags 1

prop_RDWR : Property
prop_RDWR = property1 $ RDWR === MkFlags 2

prop_APPEND : Property
prop_APPEND = property1 $ APPEND === MkFlags 1024

prop_CREAT : Property
prop_CREAT = property1 $ CREAT === MkFlags 64

prop_IRWXU : Property
prop_IRWXU = property1 $ S_IRWXU === MkMode 448

prop_IRUSR : Property
prop_IRUSR = property1 $ S_IRUSR === MkMode 256

prop_IWUSR : Property
prop_IWUSR = property1 $ S_IWUSR === MkMode 128

prop_IXUSR : Property
prop_IXUSR = property1 $ S_IXUSR === MkMode 64

prop_IRWXG : Property
prop_IRWXG = property1 $ S_IRWXG === MkMode 56

prop_IRGRP : Property
prop_IRGRP = property1 $ S_IRGRP === MkMode 32

prop_IWGRP : Property
prop_IWGRP = property1 $ S_IWGRP === MkMode 16

prop_IXGRP : Property
prop_IXGRP = property1 $ S_IXGRP === MkMode 8

prop_IRWXO : Property
prop_IRWXO = property1 $ S_IRWXO === MkMode 7

prop_IROTH : Property
prop_IROTH = property1 $ S_IROTH === MkMode 4

prop_IWOTH : Property
prop_IWOTH = property1 $ S_IWOTH === MkMode 2

prop_IXOTH : Property
prop_IXOTH = property1 $ S_IXOTH === MkMode 1

export
props : Group
props =
  MkGroup "Flags"
    [ ("prop_WRONLY", prop_WRONLY)
    , ("prop_RDONLY", prop_RDONLY)
    , ("prop_RDWR",   prop_RDWR)
    , ("prop_APPEND", prop_APPEND)
    , ("prop_CREAT",  prop_CREAT)
    , ("prop_IRWXU",  prop_IRWXU)
    , ("prop_IRUSR",  prop_IRUSR)
    , ("prop_IWUSR",  prop_IWUSR)
    , ("prop_IXUSR",  prop_IXUSR)
    , ("prop_IRWXG",  prop_IRWXG)
    , ("prop_IRGRP",  prop_IRGRP)
    , ("prop_IWGRP",  prop_IWGRP)
    , ("prop_IXGRP",  prop_IXGRP)
    , ("prop_IRWXO",  prop_IRWXO)
    , ("prop_IROTH",  prop_IROTH)
    , ("prop_IWOTH",  prop_IWOTH)
    , ("prop_IXOTH",  prop_IXOTH)
    ]

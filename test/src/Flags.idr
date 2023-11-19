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

export
props : Group
props =
  MkGroup "Flags"
    [ ("prop_WRONLY", prop_WRONLY)
    , ("prop_RDONLY", prop_RDONLY)
    , ("prop_RDWR",   prop_RDWR)
    , ("prop_APPEND", prop_APPEND)
    , ("prop_CREAT",  prop_CREAT)
    ]

-- printf("%d\n", O_RDONLY);
-- printf("%d\n", O_WRONLY);
-- printf("%d\n", O_RDWR);
-- printf("%d\n", O_APPEND);
-- printf("%d\n", O_CREAT);
-- printf("%d\n", S_IRWXU);
-- printf("%d\n", S_IRUSR);
-- printf("%d\n", S_IWUSR);
-- printf("%d\n", S_IXUSR);
-- printf("%d\n", S_IRWXG);
-- printf("%d\n", S_IRGRP);
-- printf("%d\n", S_IWGRP);
-- printf("%d\n", S_IXGRP);
-- printf("%d\n", S_IRWXO);
-- printf("%d\n", S_IROTH);
-- printf("%d\n", S_IWOTH);
-- printf("%d\n", S_IXOTH);

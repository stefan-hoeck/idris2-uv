# Rx Examples

```idris
module Docs.UV.Rx

import Data.List
import Data.String
import Data.Buffer.Indexed
import System.Rx.Core
import System.Rx.Pipe
import System.UV

main : IO ()
main =
  runUV $
      timer 1 1
  |>  dropErrs
  |>  zipWithIndex
  |>  drop 10
  |>  take 500
  |>  showLines
  |>  bytes
  |>> appendToFile "test.txt"
```

<!-- vi: filetype=idris2:syntax=markdown
-->

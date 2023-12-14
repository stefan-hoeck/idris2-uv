# Rx Examples

```idris
module Docs.UV.Rx

import Data.List
import Data.String
import Data.Buffer.Indexed
import System.Rx
import System.UV

read : IO ()
read =
  runUV $
       readFile "/home/gundi/documents/zinc/zinc2.smi"
    |> printErrs
    |>> toFile "/home/gundi/idris/uv/out.smi"

timer : IO ()
timer =
  runUV $
        timer 1 1
    |>  dropErrs
    |>  zipWithIndex
    |>  drop 10
    |>  take 500
    |>  showLines
    |>  bytes
    |>> appendToFile "test.txt"

main : IO ()
main = read
```

<!-- vi: filetype=idris2:syntax=markdown
-->

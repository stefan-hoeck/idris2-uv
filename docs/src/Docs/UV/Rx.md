# Rx Examples

```idris
module Docs.UV.Rx

import Data.List
import Data.String
import Data.Buffer.Indexed
import System.Rx
import System.UV
import System

fileNames : List String -> List String
fileNames (_::t) = t
fileNames []     = []

cat : IO ()
cat = do
  args <- getArgs
  runUV $
        batch (fileNames args)
    |>  flatMap readFile
    |>  printErrs
    |>> toFile "out.txt"

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
main = cat
```

<!-- vi: filetype=idris2:syntax=markdown
-->

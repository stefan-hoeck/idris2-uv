# Rx Examples

```idris
module Docs.UV.Rx

import Data.List
import Data.String
import Data.Buffer.Indexed
import Data.ByteString
import Data.ByteVect
import System.Rx
import System.UV
import System.UV.Pipe
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

readIn : IO ()
readIn = do
  runUV $
        streamStdin
    |>  printErrs
    |>  snocBuffer 0xffff
    |>  lines
    |>  count
    |>  showLines
    |>  bytes
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
main = readIn
```

<!-- vi: filetype=idris2:syntax=markdown
-->

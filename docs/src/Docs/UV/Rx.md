# Rx Examples

```idris
module Docs.UV.Rx

import System.Rx.Core
import System.Rx.Pipe
import System.UV

main : IO ()
main =
  runUV $ do
  liftIO (timer 1000 1000 |> dropErrs |> take 10 |> const "hello rx" |>> putOutLn)
```

<!-- vi: filetype=idris2:syntax=markdown
-->

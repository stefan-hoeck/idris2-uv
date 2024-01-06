# Monad Async

```idris
module Docs.UV.Async

import Data.IORef
import System.UV
import System.UV.Idle
import System.UV.Timer

0 DocIO : Type -> Type
DocIO = Async [UVError]

handles : All (\x => x -> Async [] ()) [UVError]
handles = [printLn]

checkCounter : UVLoop => (stop : Integer) -> IORef Integer -> DocIO (Maybe ())
checkCounter stop ref = do
  modifyIORef ref (+1)
  v <- readIORef ref
  when (v `mod` 10000 == 0) (putOutLn "Counter is at \{show v}")
  pure $ if v >= stop then Just () else Nothing

idleExample : IO ()
idleExample =
  runUV $ runAsync $ handle handles $ do
    ref     <- newIORef 0
    counter <- onIdle (checkCounter 80000 ref)
    -- _       <- once 100 (putStrLn "canceling counter" >> counter.cancel)
    pure ()

main : IO ()
main = idleExample
```

<!-- vi: filetype=idris2:syntax=markdown
-->

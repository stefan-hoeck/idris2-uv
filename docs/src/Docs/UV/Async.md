# Monad Async

```idris
module Docs.UV.Async

import Data.IORef
import System.UV
import System.UV.Idle
import System.UV.Signal
import System.UV.Timer

0 DocIO : Type -> Type
DocIO = Async [UVError]

handles : All (\x => x -> Async [] ()) [UVError]
handles = [printLn]

runDoc : (UVLoop => DocIO ()) -> IO ()
runDoc doc = runUV $ runAsync (handle handles doc)

parameters {auto l : UVLoop}

  checkCounter : IORef Integer -> DocIO (Maybe ())
  checkCounter ref = do
    modifyIORef ref (+1)
    v <- readIORef ref
    when (v `mod` 10000 == 0) (putOutLn "Counter is at \{show v}")
    pure Nothing

  idleExample : DocIO ()
  idleExample = do
    ref     <- newIORef 0
    pp      <- mkIdle
    counter <- onIdle (checkCounter ref)
    _       <- onSignal SIGINT (\_ => putStrLn "canceling counter" >> counter.cancel)
    pure ()

main : IO ()
main = runDoc idleExample
```

<!-- vi: filetype=idris2:syntax=markdown
-->

# Monad Async

```idris
module Docs.UV.Async

import Data.IORef
import System
import System.UV
import System.UV.Idle
import System.UV.Signal
import System.UV.Timer

0 DocIO : Type -> Type
DocIO = Async [UVError]

handles : All (\x => x -> Async [] ()) [UVError]
handles = [putStrLn . interpolate]

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

    res     <- raceEither (onSignal SIGINT) (once 5000)

    case res of
      Left sig => putOutLn "Counter interrupted by \{show sig}"
      Right () => putOutLn "Counter interrupted by timeout"

    putOutLn "Cancelling counter"
    cancel

  readExample : DocIO ()
  readExample = do
    (_::p::_) <- getArgs | _ => putErrLn "Invalid number of arguments"
    readFile p 0xffff >>= bytesOut

  fileStreamExample : DocIO ()
  fileStreamExample = do
    (_::p::_) <- getArgs | _ => putErrLn "Invalid number of arguments"
    v <- raceEither (onSignal SIGINT) (streamFile p 0xfffff bytesOut)
    case v of
      Left s  => putOutLn "\nStream interrupted by \{show s}"
      Right _ => putOutLn "\nStream exhausted."

main : IO ()
main = runDoc fileStreamExample
```

<!-- vi: filetype=idris2:syntax=markdown
-->

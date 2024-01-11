# Monad Async

```idris
module Docs.UV.Async

import Data.IORef
import System
import System.File
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

  fileStreamExample : DocIO ()
  fileStreamExample = do
    (_::p::_) <- getArgs | _ => putErrLn "Invalid number of arguments"
    v <- use1 (fsOpen "out" (WRONLY <+> CREAT) 0o644) $ \f =>
           raceEither (onSignal SIGINT) (streamFile p 0xffff $ writeBytes f)
    case v of
      Left s  => putOutLn "Stream interrupted by \{show s}"
      Right _ => putOutLn "Stream exhausted."

main : IO ()
main = runDoc fileStreamExample
```

<!-- vi: filetype=idris2:syntax=markdown
-->

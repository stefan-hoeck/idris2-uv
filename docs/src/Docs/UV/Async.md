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

  readTest : String -> Nat -> DocIO ByteString
  readTest p n =
    uvAsync $ \cb => do
      Right bs <- withFile p Read pure $ readByteString n
        | Left err => cb (Succeeded empty) $> 0
      cb (Succeeded bs)
      pure 0

  readExample : DocIO ()
  readExample = do
    (_::p::_) <- getArgs | _ => putErrLn "Invalid number of arguments"
    readTest p 0xfffff >>= bytesOut

  test : Nat -> DocIO ()
  test 0  = pure ()
  test (S k) = do
    readExample
    test k

  fileStreamExample : DocIO ()
  fileStreamExample = do
    (_::t) <- getArgs | _ => putErrLn "Invalid number of arguments"
    for_ t $ \f => ignore $ streamFile f 0xfffff
    -- v <- raceEither (onSignal SIGINT) (streamFile p 0xfffff $ \b => pure ())
    -- case v of
    --   Left s  => putOutLn "\nStream interrupted by \{show s}"
    --   Right _ => putOutLn "\nStream exhausted."

main : IO ()
main = runDoc $ test 10000
```

<!-- vi: filetype=idris2:syntax=markdown
-->

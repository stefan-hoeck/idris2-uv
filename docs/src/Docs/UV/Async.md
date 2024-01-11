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

  readExample : String -> DocIO ()
  readExample p = do
    readFile p 0xfffff >>= \_ => pure ()

  test : String -> Nat -> DocIO ()
  test p 0  = pure ()
  test p (S k) = do
    readExample p
    test p k

  fileStreamExample : DocIO ()
  fileStreamExample = do
    (_::p::_) <- getArgs | _ => putErrLn "Invalid number of arguments"
    -- for_ t $ \f => ignore $ streamFile f 0xfffff
    v <- raceEither (onSignal SIGINT) (streamFile p 0xfffff bytesOut)
    case v of
      Left s  => putOutLn "\nStream interrupted by \{show s}"
      Right _ => putOutLn "\nStream exhausted."

main : IO ()
main = do
  (_::p::_) <- getArgs | _ => putStrLn "Invalid number of arguments"
  runDoc $ test p 40000
```

<!-- vi: filetype=idris2:syntax=markdown
-->
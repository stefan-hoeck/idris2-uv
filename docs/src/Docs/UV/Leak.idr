module Docs.UV.Leak

import Data.Buffer.Indexed
import Data.ByteString
import Data.IORef
import System
import System.UV.Raw.Callback
import System.UV.Raw.File
import System.UV.Raw.Handle
import System.UV.Raw.Loop
import System.UV.Raw.Pointer

%default total

test : Ptr Loop -> IORef FsCB -> IORef Nat -> IO ()
test loop fscb counter = do
  S k    <- readIORef counter | 0 => pure ()
  c      <- readIORef fscb
  fs     <- mallocPtr Fs
  let bs := the ByteString $ fromString . (++ "\n") . show $ S k
  buf    <- toBuffer bs
  writeIORef counter k
  ignore $ uv_fs_write_async loop fs 1 buf (cast bs.size) (-1) c

testSync : Ptr Loop -> Nat -> IO ()
testSync loop 0 = pure ()
testSync loop (S k) = do
  fs     <- mallocPtr Fs
  let bs := the ByteString $ fromString . (++ "\n") . show $ S k
  buf    <- toBuffer bs
  ignore $ uv_fs_write_async loop fs 1 buf (cast bs.size) (-1) nullCB
  freePtr fs
  testSync loop k

cb : IORef FsCB -> IORef Nat -> Ptr Loop -> Ptr Fs -> IO ()
cb fscb counter loop fs = do
  uv_fs_req_cleanup fs
  freePtr fs
  test loop fscb counter

count : IO Nat
count = do
  getArgs >>= \case
    (_::p::_) => pure $ cast p
    _         => pure 10

main : IO ()
main = do
  putStrLn "Hello async"
  loop    <- uv_default_loop
  putStrLn "Initialized loop"
  counter <- count >>= newIORef
  putStrLn "Initialized counter"
  cbRef   <- newIORef {a = FsCB} nullCB
  putStrLn "Initialized cb ref"
  fscl    <- fsCB (cb cbRef counter loop)
  writeIORef cbRef fscl
  test loop cbRef counter
  _ <- uv_run loop 0
  testSync loop 20
  pure ()

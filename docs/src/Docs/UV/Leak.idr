module Docs.UV.Leak

import Data.Buffer.Indexed
import Data.ByteString
import Data.IORef
import System
import System.UV.Raw.File
import System.UV.Raw.Handle
import System.UV.Raw.Loop
import System.UV.Raw.Pointer

%default total

test : Ptr Loop -> IORef (Ptr FsCallable) -> IORef Nat -> IO ()
test loop fscb counter = do
  S k    <- readIORef counter | 0 => pure ()
  c      <- readIORef fscb
  fs     <- mallocPtr Fs
  let bs := the ByteString $ fromString . (++ "\n") . show $ S k
  buf    <- toBuffer bs
  writeIORef counter k
  ignore $ uv_fs_write_async loop fs 1 buf (cast bs.size) (-1) (fsCB c)

cb : IORef (Ptr FsCallable) -> IORef Nat -> Ptr Loop -> Ptr Fs -> IO ()
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
  cbRef   <- newIORef {a = Ptr FsCallable} (fsCallable $ \x => toPrim $ pure ())
  putStrLn "Initialized cb ref"
  let fscl := fsCallable (\x => toPrim $ cb cbRef counter loop x)
  writeIORef cbRef fscl
  test loop cbRef counter
  _ <- uv_run loop 0
  pure ()

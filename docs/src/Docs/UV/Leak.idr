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

cb : Nat -> Ptr Loop -> Ptr Fs -> IO ()

testAsync : Nat -> Ptr Loop -> IO ()
testAsync 0     loop = pure ()
testAsync (S k) loop = do
  let bs := the ByteString $ fromString . (++ "\n") . show $ S k
  buf <- toBuffer bs
  ignore $ async (uv_fs_write loop 1 buf (cast bs.size) (-1)) (cb k loop)

testSync : Nat -> Ptr Loop -> IO ()
testSync 0     loop = pure ()
testSync (S k) loop = do
  let bs := the ByteString $ fromString . (++ "\n") . show $ S k
  buf    <- toBuffer bs
  ignore . sync $ uv_fs_write loop 1 buf (cast bs.size) (-1)
  testSync k loop

cb counter loop _ = testAsync counter loop

count : IO Nat
count = do
  getArgs >>= \case
    (_::p::_) => pure $ cast p
    _         => pure 10

main : IO ()
main = do
  loop    <- uv_default_loop
  counter <- count
  testAsync counter loop
  _ <- uv_run loop 0
  pure ()

module Docs.UV.Leak

import Data.IORef
import Data.Buffer.Indexed
import Data.ByteString
import System.UV
import System.UV.Raw.File
import System.UV.Raw.Idle
import System.UV.Raw.Loop
import System

%default total

--------------------------------------------------------------------------------
-- Sync writing
--------------------------------------------------------------------------------

-- this shows no leaking of memory
sync : Ptr Loop -> ByteString -> IO Int32
sync l bs = do
  buf <- toBuffer bs
  uv_fs_write_sync l 1 buf (cast bs.size) (-1)

testSyncLeak : Ptr Loop -> Nat -> IO ()
testSyncLeak l 0     = pure ()
testSyncLeak l (S k) = do
  ignore $ sync l (fromString . (++ "\n") . show $ S k)
  testSyncLeak l k

--------------------------------------------------------------------------------
-- Async writing
--------------------------------------------------------------------------------

async : Ptr Loop -> ByteString -> Ptr Bits8 -> IO Int32
async l bs tag = do
  buf <- toBuffer bs
  uv_fs_write_cb l 1 buf (cast bs.size) (-1) tag

idler : Ptr Loop -> Ptr Bits8 -> IORef Nat -> Ptr Idle -> IO ()
idler l ready cnt pi = do
  1 <- uv_ready ready | _ => pure ()
  S k  <- readIORef cnt | 0 => ignore (uv_idle_stop pi)
  uv_clear_ready ready
  writeIORef cnt k
  ignore $ async l (fromString . (++ "\n") . show $ S k) ready

count : IO Nat
count =
  getArgs >>= \case
    (_::n::_) => pure $ cast n
    _         => pure 10
main : IO ()
main = do
  putStrLn "Hello world"
  cnt   <- count >>= newIORef
  l <- uv_default_loop
  i <- mallocPtr Idle
  r <- mallocPtr Bits8
  uv_set_ready r
  _  <- uv_idle_init l i
  _  <- uv_idle_start i $ idler l r cnt
  r2 <- uv_run l 0
  pure ()

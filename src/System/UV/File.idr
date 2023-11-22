module System.UV.File

import Data.Buffer.Indexed
import Data.ByteString
import Control.Monad.Either
import Data.Buffer
import System.FFI
import System.UV.Error
import System.UV.File.Flags
import System.UV.Handle
import System.UV.Loop
import System.UV.Req
import System.UV.Util

%default total

||| A `Ptr Buf` corresponst to an `un_buf_t` pointer
export
data Buf : Type where

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "scheme:blodwen-new-buffer"
         "node:lambda:s=>Buffer.alloc(s)"
prim__newBuf : Bits32 -> PrimIO Buffer

%foreign (idris_uv "uv_init_buf")
prim__uv_init_buf : Bits32 -> PrimIO (Ptr Buf)

%foreign (idris_uv "uv_set_buf_len")
prim__uv_set_buf_len : Ptr Buf -> Bits32 -> PrimIO ()

%foreign (idris_uv "uv_free_buf")
prim__uv_free_buf : Ptr Buf -> PrimIO ()

%foreign (idris_uv "uv_fs_get_result")
prim__uv_fs_get_result : Ptr Fs -> PrimIO Int64

%foreign (idris_uv "uv_copy_buf")
prim__uv_copy_to_buf : Ptr Buf -> Buffer -> Bits32 -> PrimIO ()

%foreign (idris_uv "uv_copy_buf")
prim__uv_copy_from_buf : Buffer -> Ptr Buf -> Bits32 -> PrimIO ()

%foreign (idris_uv "uv_fs_req_cleanup")
prim__uv_fs_req_cleanup : Ptr Fs -> PrimIO ()

%foreign (idris_uv "uv_fs_open")
prim__uv_fs_open :
     Ptr LoopPtr
  -> Ptr Fs
  -> String
  -> (flags,mode : Bits32)
  -> (cb : Ptr Fs -> PrimIO ())
  -> PrimIO Int64

%foreign (idris_uv "uv_fs_read")
prim__uv_fs_read :
     Ptr LoopPtr
  -> Ptr Fs
  -> (file   : Int64)
  -> (bufs   : Ptr Buf)
  -> (nbufs  : Bits32)
  -> (offset : Int64)
  -> (cb     : Ptr Fs -> PrimIO ())
  -> PrimIO Int64

%foreign (idris_uv "uv_fs_write")
prim__uv_fs_write :
     Ptr LoopPtr
  -> Ptr Fs
  -> (file   : Int64)
  -> (bufs   : Ptr Buf)
  -> (nbufs  : Bits32)
  -> (offset : Int64)
  -> (cb     : Ptr Fs -> PrimIO ())
  -> PrimIO Int64

%foreign (idris_uv "uv_fs_close")
prim__uv_fs_close :
     Ptr LoopPtr
  -> Ptr Fs
  -> (file : Int64)
  -> (cb   : Ptr Fs -> PrimIO ())
  -> PrimIO Int64

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Frees a file reading buffer allocated with `allocBuf`.
export %inline
freeBuf : HasIO io => Ptr Buf -> io ()
freeBuf p = primIO $ prim__uv_free_buf p

||| Allocate a buffer for file reading. Make sure to release this with
||| `freeBuf` once it is no longer needed.
export %inline
allocBuf : HasIO io => Bits32 -> io (Ptr Buf)
allocBuf p = primIO $ prim__uv_init_buf p

export %inline
setBufLen : HasIO io => Ptr Buf -> Bits32 -> io ()
setBufLen p len = primIO $ prim__uv_set_buf_len p len

||| Returns the result code received after a file operation.
export %inline
fsResult : HasIO io => Ptr Fs -> io Int64
fsResult p = primIO $ prim__uv_fs_get_result p

||| Synchronously closes a file and releases the file handle.
|||
||| Once the file is closed, the given `IO` action is invoked.
export %inline
fsClose : (l : Loop) => Ptr Fs -> Int64 -> (Ptr Fs -> IO ()) -> UVIO ()
fsClose fs h run = do
  primUV $ prim__uv_fs_close l.loop fs h (\p => toPrim $ run p)

||| Asynchronously opens a file, invoking the given callback once
||| the file is ready.
export %inline
fsOpen :
     {auto l : Loop}
  -> Ptr Fs
  -> String
  -> Flags
  -> Mode
  -> (Ptr Fs -> IO ())
  -> UVIO ()
fsOpen ptr path fs m act = do
  primUV $ prim__uv_fs_open l.loop ptr path fs.flags m.mode $
    \p => toPrim (act p)

||| Reads data from a file into the given buffer and invokes
||| the callback function once the data is ready.
export
fsRead :
     {auto l : Loop}
  -> Ptr Fs
  -> (file   : Int64)
  -> (bufs   : Ptr Buf)
  -> (nbufs  : Bits32)
  -> (offset : Int64)
  -> (cb     : Ptr Fs -> IO ())
  -> UVIO ()
fsRead f h bufs nbufs offset act =
  primUV $ prim__uv_fs_read l.loop f h bufs nbufs offset $
    \fp => toPrim (act fp)

||| Writes data from the given buffer to a file and invokes
||| the callback function once the data is ready.
export
fsWrite :
     {auto l : Loop}
  -> Ptr Fs
  -> (file   : Int64)
  -> (bufs   : Ptr Buf)
  -> (nbufs  : Bits32)
  -> (offset : Int64)
  -> (cb     : Ptr Fs -> IO ())
  -> UVIO ()
fsWrite f h bufs nbufs offset act =
  primUV $ prim__uv_fs_write l.loop f h bufs nbufs offset $
    \fp => toPrim (act fp)

||| Copies data from a byte array handled by libuv to an
||| Idris buffer.
|||
||| This comes without sanity checks. Callers must make sure that
||| both byte arrays hold at least the given number of bytes.
export %inline
copyToBuffer : HasIO io => Ptr Buf -> Buffer -> Bits32 -> io ()
copyToBuffer p buf bytes = primIO $ prim__uv_copy_to_buf p buf bytes

||| Copies data from a byte array handled by libuv to an
||| Idris buffer.
|||
||| This comes without sanity checks. Callers must make sure that
||| both byte arrays hold at least the given number of bytes.
export %inline
copyFromBuffer : HasIO io => Buffer -> Ptr Buf -> Bits32 -> io ()
copyFromBuffer buf p bytes = primIO $ prim__uv_copy_from_buf buf p bytes

export %inline
fsCleanup : HasIO io => Ptr Fs -> io ()
fsCleanup fp = primIO $ prim__uv_fs_req_cleanup fp

-- export
-- fileRead :
--      {auto l : Loop}
--   -> UFile
--   -> (numBytes : Bits32)
--   -> (position : Int64)
--   -> (Either UVError ByteString -> IO ())
--   -> UVIO ()
-- fileRead @{MkLoop l} (MkUFile f h) numBytes pos act = MkEitherT $ do
--   buf <- primIO $ prim__initBuf numBytes
--   res <- primIO $ prim__uv_fs_read l f h buf pos $ \fp => toPrim $ do 
--     n <- fileRes fp 
--     if n == 0
--        then act (Right empty)
--        else
--          if n < 0
--             then act (Left $ fromCode n)
--             else copyData buf (cast n) >>= act . Right
--     primIO $ prim__uv_fs_req_cleanup fp
--     freeBuf buf
--   when (res < 0) (freeBuf buf)
--   pure $ uvRes res
-- 
-- export
-- read :
--      {auto l : Loop}
--   -> String
--   -> (numBytes : Bits32)
--   -> (Either UVError ByteString -> IO ())
--   -> UVIO ()
-- read path nb act = do
--   fileOpen path RDONLY neutral $ \fp =>
--     runUVIO $ fileRead fp nb 0 (\res => fileClose fp >> act res)
-- 
-- --------------------------------------------------------------------------------
-- -- Streaming
-- --------------------------------------------------------------------------------
-- 
-- public export
-- data StreamRes : (a : Type) -> Type where
--   Err   : UVError -> StreamRes a
--   Empty : StreamRes a
--   Val   : a -> StreamRes a
-- 
-- public export
-- data Continue = Cont | Stop
-- 
-- public export
-- 0 StreamResp : (s : StreamRes a) -> Type
-- StreamResp (Err x) = ()
-- StreamResp Empty   = ()
-- StreamResp (Val x) = Continue
-- 
-- export covering
-- stream :
--      {auto l : Loop}
--   -> String
--   -> (numBytes : Bits32)
--   -> ((s : StreamRes ByteString) -> IO (StreamResp s))
--   -> UVIO ()
-- stream path nb act = do
--   buf <- primIO $ prim__initBuf nb
--   fileOpen path RDONLY neutral (go buf)
-- 
--   where
--     cleanup : Ptr Buf -> UFile -> IO ()
--     cleanup buf fi = fileClose fi >> freeBuf buf
-- 
--     covering
--     go : Ptr Buf -> UFile -> IO ()
--     go buf fi@(MkUFile f h) = do
--       res <- primIO $ prim__uv_fs_read l.loop f h buf (-1) $ \fp => toPrim $ do
--         n <- fileRes fp 
--         cleanupFP fp
--         if n == 0
--            then cleanup buf fi >> act Empty
--            else
--              if n < 0
--                 then cleanup buf fi >> act (Err $ fromCode n)
--                 else do
--                   bs <- copyData buf (cast n)
--                   Cont <- act (Val bs) | Stop => cleanup buf fi 
--                   go buf fi
--       when (res < 0) (cleanup buf fi >> act (Err $ fromCode res))

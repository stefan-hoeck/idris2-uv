module System.UV.File

import Data.Buffer.Indexed
import Data.ByteString
import Data.Buffer
import System.FFI
import System.UV.Error
import System.UV.File.Flags
import System.UV.Handle
import System.UV.Loop
import System.UV.Pointer
import System.UV.Util

%default total

||| A file handle.
public export
record File where
  constructor MkFile
  file : Int32

export %inline
stdin : File
stdin = MkFile 0

export %inline
stdout : File
stdout = MkFile 1

export %inline
stderr : File
stderr = MkFile 2

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "scheme:blodwen-new-buffer"
         "node:lambda:s=>Buffer.alloc(s)"
prim__newBuf : Bits32 -> PrimIO Buffer

%foreign (idris_uv "uv_fs_get_result")
prim__uv_fs_get_result : Ptr Fs -> PrimIO Int32

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
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_read")
prim__uv_fs_read :
     Ptr LoopPtr
  -> Ptr Fs
  -> (file   : Int32)
  -> (bufs   : Ptr Buf)
  -> (nbufs  : Bits32)
  -> (offset : Int32)
  -> (cb     : Ptr Fs -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_write")
prim__uv_fs_write :
     Ptr LoopPtr
  -> Ptr Fs
  -> (file   : Int32)
  -> (bufs   : Ptr Buf)
  -> (nbufs  : Bits32)
  -> (offset : Int32)
  -> (cb     : Ptr Fs -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_close")
prim__uv_fs_close :
     Ptr LoopPtr
  -> Ptr Fs
  -> (file : Int32)
  -> (cb   : Ptr Fs -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_close_sync")
prim__uv_fs_close_sync : Ptr LoopPtr -> (file : Int32) -> PrimIO Int32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Creates a new byte vector of the given size.
|||
||| Note: On the scheme backends, the returned buffer is managed by the runtime
|||       so it needs not be released manually.
export %inline
newBuffer : HasIO io => Bits32 -> io Buffer
newBuffer size = primIO $ prim__newBuf size

||| Returns the result code received after a file operation.
export %inline
fsResult : HasIO io => Ptr Fs -> io Int32
fsResult p = primIO $ prim__uv_fs_get_result p

||| Returns the file handle associated with an `uv_fs_t` handle.
|||
||| This reads the same field as `fsResult` but interprets a negative
||| number as an error and a non-negative result as a file handle.
export
fsFile : HasIO io => Ptr Fs -> io (Either UVError File)
fsFile p = do
  n <- fsResult p
  pure $ if n < 0 then Left (fromCode n) else Right (MkFile n)

||| Asynchronously closes a file and releases the file handle.
|||
||| Once the file is closed, the given `IO` action is invoked.
||| Note: Consider using the synchronous version `fsClose` instead for simplicity.
|||       Closing a file will probably not have a significant blocking effect.
export %inline
fsCloseAsync : (l : Loop) => Ptr Fs -> File -> (Ptr Fs -> IO ()) -> UVIO ()
fsCloseAsync fs h run = do
  primUV $ prim__uv_fs_close l.loop fs h.file (\p => toPrim $ run p)

||| Synchronously closes a file and releases the file handle.
export %inline
fsClose : (l : Loop) => File -> UVIO ()
fsClose h = primUV $ prim__uv_fs_close_sync l.loop h.file

||| Asynchronously opens a file, invoking the given callback once
||| the file is ready.
|||
||| This is a faithful binding to `uv_fs_open`. What you typicall want is
||| to use the file handle (if any) or an error message in the callback
||| and work with that. For that, there is `fsOpen` as a more convenient
||| version.
export %inline
fsOpenRaw :
     {auto l : Loop}
  -> Ptr Fs
  -> String
  -> Flags
  -> Mode
  -> (Ptr Fs -> IO ())
  -> UVIO ()
fsOpenRaw ptr path fs m act = do
  primUV $ prim__uv_fs_open l.loop ptr path fs.flags m.mode $
    \p => toPrim (act p)

||| Asynchronously opens a file, invoking the given callback once
||| the file is ready.
export %inline
fsOpen :
     {auto l : Loop}
  -> Ptr Fs
  -> String
  -> Flags
  -> Mode
  -> (Either UVError File -> IO ())
  -> UVIO ()
fsOpen ptr path fs m act =
  fsOpenRaw ptr path fs m $ \p => fsFile p >>= act

||| Reads data from a file into the given buffer and invokes
||| the callback function once the data is ready.
|||
||| This is a faithful binding to `uv_fs_read`. What you typically want is
||| to decide on the return value stored in the `Ptr Fs` you get to figure
||| out what to do next. For that, there is `fsRead` as a more convenient
||| version.
export %inline
fsReadRaw :
     {auto l : Loop}
  -> Ptr Fs
  -> (file   : File)
  -> (bufs   : Ptr Buf)
  -> (nbufs  : Bits32)
  -> (offset : Int32)
  -> (cb     : Ptr Fs -> IO ())
  -> UVIO ()
fsReadRaw f h bufs nbufs offset act =
  primUV $ prim__uv_fs_read l.loop f h.file bufs nbufs offset $
    \fp => toPrim (act fp)

public export
data ReadRes : (a : Type) -> Type where
  Err    : UVError -> ReadRes s
  NoData : ReadRes a
  Data   : a -> ReadRes a

export
codeToRes : Int32 -> ReadRes Bits32
codeToRes 0 = NoData
codeToRes n = if n < 0 then Err (fromCode n) else Data (cast n)

||| Convenience version of `fsReadRaw` where the amount of
||| data read is analyzed and passed as a data type to the callback.
export
fsRead :
     {auto l : Loop}
  -> Ptr Fs
  -> (file   : File)
  -> (bufs   : Ptr Buf)
  -> (nbufs  : Bits32)
  -> (offset : Int32)
  -> (cb     : ReadRes Bits32 -> IO ())
  -> UVIO ()
fsRead f h bufs nbufs offset act = do
  fsReadRaw f h bufs nbufs offset $ \req => do
    n <- fsResult req
    act $ codeToRes n

||| Writes data from the given buffer to a file and invokes
||| the callback function once the data is ready.
|||
||| This is a faithful binding to `uv_fs_write`. What you typically want is
||| to decide on the return value stored in the `Ptr Fs` you get to figure
||| out what to do next. For that, there is `fsWrite` as a more convenient
||| version.
export %inline
fsWriteRaw :
     {auto l : Loop}
  -> Ptr Fs
  -> (file   : File)
  -> (bufs   : Ptr Buf)
  -> (nbufs  : Bits32)
  -> (offset : Int32)
  -> (cb     : Ptr Fs -> IO ())
  -> UVIO ()
fsWriteRaw f h bufs nbufs offset act =
  primUV $ prim__uv_fs_write l.loop f h.file bufs nbufs offset $
    \fp => toPrim (act fp)

||| Convenience version of `fsWriteRaw` where the write result
||| is analyzed and passed as a potential error to the callback.
export
fsWrite :
     {auto l : Loop}
  -> Ptr Fs
  -> (file   : File)
  -> (bufs   : Ptr Buf)
  -> (nbufs  : Bits32)
  -> (offset : Int32)
  -> (cb     : Maybe UVError -> IO ())
  -> UVIO ()
fsWrite f h bufs nbufs offset act =
  fsWriteRaw f h bufs nbufs offset $ \req => do
    n <- fsResult req
    if n < 0 then act (Just $ fromCode n) else act Nothing

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
--   -> (position : Int32)
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

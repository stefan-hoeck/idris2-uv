module System.UV.File

import Data.Buffer.Indexed
import Data.ByteString
import Control.Monad.Either
import Data.Buffer
import System.FFI
import System.UV.Error
import System.UV.File.Flags
import System.UV.Loop
import System.UV.Util

%default total

||| A `Ptr FSPtr` corresponst to an `un_fs_t` pointer
export
data FSPtr : Type where

||| Data type wrapping a pointer to an `uv_fs_t` struct and a file handle.
public export
record UFile where
  constructor MkUFile
  fs     : Ptr FSPtr
  handle : Int64

||| A `Ptr BufPtr` corresponst to an `un_buf_t` pointer
export
data BufPtr : Type where

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "scheme:blodwen-new-buffer"
         "node:lambda:s=>Buffer.alloc(s)"
prim__newBuf : Bits32 -> PrimIO Buffer

%foreign (idris_uv "uv_alloc_fs")
prim__allocFS : PrimIO (Ptr FSPtr)

%foreign (idris_uv "uv_init_buf")
prim__initBuf : Bits32 -> PrimIO (Ptr BufPtr)

%foreign (idris_uv "uv_free_buf")
prim__freeBuf : Ptr BufPtr -> PrimIO ()

%foreign (idris_uv "uv_fs_result")
prim__fileResult : Ptr FSPtr -> PrimIO Int64

%foreign (idris_uv "uv_copy_buf")
prim__copyBuf : Ptr BufPtr -> Buffer -> PrimIO ()

%foreign (idris_uv "uv_fs_req_cleanup")
prim__uv_fs_req_cleanup : Ptr FSPtr -> PrimIO ()

%foreign (idris_uv "uv_fs_open")
prim__fileOpen :
     Ptr LoopPtr
  -> Ptr FSPtr
  -> String
  -> (flags,mode : Bits32)
  -> (cb : Ptr FSPtr -> PrimIO ())
  -> PrimIO Int64

%foreign (idris_uv "uv_read_fs")
prim__fileRead :
     Ptr LoopPtr
  -> Ptr FSPtr
  -> (file   : Int64)
  -> (buf    : Ptr BufPtr)
  -> (offset : Int64)
  -> (cb : Ptr FSPtr -> PrimIO ())
  -> PrimIO Int64

%foreign (idris_uv "uv_fs_close")
prim__fileClose :
     Ptr LoopPtr
  -> Ptr FSPtr
  -> (file : Int64)
  -> (cb : Ptr FSPtr -> PrimIO ())
  -> PrimIO Int64

%foreign (idris_uv "uv_fs_req_cleanup")
prim__fsReqCleanup : Ptr FSPtr -> PrimIO ()

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Free the memory allocated for an `uv_fs_t` pointer.
export %inline
freeBuf : HasIO io => Ptr BufPtr -> io ()
freeBuf p = primIO $ prim__freeBuf p

fileRes : HasIO io => Ptr FSPtr -> io Int64
fileRes p = primIO $ prim__fileResult p

||| Asynchronously closes a file and releases the file handle.
|||
||| Once the file is closed, the given `IO` action is invoked.
export %inline
fileCloseWith : Loop => UFile -> IO () -> IO ()
fileCloseWith @{MkLoop p} (MkUFile fs h) run =
  ignore $ primIO $ prim__fileClose p fs h (\_ => toPrim $ free (prim__forgetPtr fs) >> run)

||| Asynchronously closes a file and releases the file handle without
||| any further action.
export %inline
fileClose : Loop => UFile -> IO ()
fileClose uf = fileCloseWith uf (pure ())

||| Asynchronously closes a file and releases the file handle without
||| any further action.
export
fileOpen : Loop => String -> Flags -> Mode -> (UFile -> IO ()) -> UVIO ()
fileOpen @{MkLoop p} path flags mode act = do
  ptr <- primIO $ prim__allocFS
  primUV $ prim__fileOpen p ptr path flags.flags mode.mode $
    \p => toPrim $ do
      h <- primIO (prim__fileResult p)
      act (MkUFile p h)

copyData : Ptr BufPtr -> Bits32 -> IO ByteString
copyData p n = do
  buf <- primIO $ prim__newBuf n
  primIO $ prim__copyBuf p buf
  pure (unsafeByteString (cast n) buf)

cleanupFP : Ptr FSPtr -> IO ()
cleanupFP fp = primIO $ prim__uv_fs_req_cleanup fp

export
fileRead :
     {auto l : Loop}
  -> UFile
  -> (numBytes : Bits32)
  -> (position : Int64)
  -> (Either UVError ByteString -> IO ())
  -> UVIO ()
fileRead @{MkLoop l} (MkUFile f h) numBytes pos act = MkEitherT $ do
  buf <- primIO $ prim__initBuf numBytes
  res <- primIO $ prim__fileRead l f h buf pos $ \fp => toPrim $ do 
    n <- fileRes fp 
    if n == 0
       then act (Right empty)
       else
         if n < 0
            then act (Left $ fromCode n)
            else copyData buf (cast n) >>= act . Right
    primIO $ prim__uv_fs_req_cleanup fp
    freeBuf buf
  when (res < 0) (freeBuf buf)
  pure $ uvRes res

export
read :
     {auto l : Loop}
  -> String
  -> (numBytes : Bits32)
  -> (Either UVError ByteString -> IO ())
  -> UVIO ()
read path nb act = do
  fileOpen path RDONLY neutral $ \fp =>
    runUVIO $ fileRead fp nb 0 (\res => fileClose fp >> act res)

--------------------------------------------------------------------------------
-- Streaming
--------------------------------------------------------------------------------

public export
data StreamRes : (a : Type) -> Type where
  Err   : UVError -> StreamRes a
  Empty : StreamRes a
  Val   : a -> StreamRes a

public export
data Continue = Cont | Stop

public export
0 StreamResp : (s : StreamRes a) -> Type
StreamResp (Err x) = ()
StreamResp Empty   = ()
StreamResp (Val x) = Continue

export covering
stream :
     {auto l : Loop}
  -> String
  -> (numBytes : Bits32)
  -> ((s : StreamRes ByteString) -> IO (StreamResp s))
  -> UVIO ()
stream path nb act = do
  buf <- primIO $ prim__initBuf nb
  fileOpen path RDONLY neutral (go buf)

  where
    covering
    go : Ptr BufPtr -> UFile -> IO ()
    go buf fi@(MkUFile f h) = do
      res <- primIO $ prim__fileRead l.loop f h buf (-1) $ \fp => toPrim $ do
        n <- fileRes fp 
        cleanupFP fp
        if n == 0
           then fileClose fi >> freeBuf buf >> act Empty
           else
             if n < 0
                then fileClose fi >> freeBuf buf >> act (Err $ fromCode n)
                else do
                  bs <- copyData buf (cast n)
                  Cont <- act (Val bs) | Stop => fileClose fi >> freeBuf buf
                  go buf fi
      when (res < 0) (fileClose fi >> freeBuf buf)
      pure ()

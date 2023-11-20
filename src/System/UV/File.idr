module System.UV.File

import Data.Buffer.Indexed
import Data.ByteString
import Control.Monad.Either
import Data.Buffer
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

%foreign (idris_uv "uv_alloc_fs")
prim__allocFS : PrimIO (Ptr FSPtr)

%foreign (idris_uv "uv_free_fs")
prim__freeFS : Ptr FSPtr -> PrimIO ()

%foreign (idris_uv "uv_init_buf")
prim__initBuf : Bits64 -> PrimIO (Ptr BufPtr)

%foreign (idris_uv "uv_free_buf")
prim__freeBuf : Ptr BufPtr -> PrimIO ()

%foreign (idris_uv "uv_fs_result")
prim__fileResult : Ptr FSPtr -> PrimIO Int64

%foreign (idris_uv "uv_fs_open")
prim__fileOpen :
     Ptr LoopPtr
  -> Ptr FSPtr
  -> String
  -> (flags,mode : Bits32)
  -> (cb : Ptr FSPtr -> IO ())
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
freeFS : HasIO io => Ptr FSPtr -> io ()
freeFS p = primIO $ prim__freeFS p

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
fileCloseWith : Loop => UFile -> IO () -> UVIO ()
fileCloseWith @{MkLoop p} (MkUFile fs h) run =
  primUV $ prim__fileClose p fs h (\_ => toPrim $ freeFS fs >> run)

||| Asynchronously closes a file and releases the file handle without
||| any further action.
export %inline
fileClose : Loop => UFile -> UVIO ()
fileClose uf = fileCloseWith uf (pure ())

||| Asynchronously closes a file and releases the file handle without
||| any further action.
export
fileOpen : Loop => String -> Flags -> Mode -> (UFile -> IO ()) -> UVIO ()
fileOpen @{MkLoop p} path flags mode act = do
  ptr <- primIO $ prim__allocFS
  primUV $ prim__fileOpen p ptr path flags.flags mode.mode $
    \p => do
      h <- primIO (prim__fileResult p)
      act (MkUFile p h)

export
fileRead :
     {auto l : Loop}
  -> UFile
  -> (numBytes : Bits64)
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
            else ?allocByteString
  when (res < 0) (freeBuf buf)
  pure $ uvRes res

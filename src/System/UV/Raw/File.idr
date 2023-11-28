module System.UV.Raw.File

import System.UV.Raw.Handle
import System.UV.Raw.Loop
import System.UV.Raw.Pointer
import System.UV.Raw.Util

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_fs_get_result")
prim__uv_fs_get_result : Ptr Fs -> PrimIO Int32

%foreign (idris_uv "uv_fs_req_cleanup")
prim__uv_fs_req_cleanup : Ptr Fs -> PrimIO ()

%foreign (idris_uv "uv_fs_open")
prim__uv_fs_open :
     Ptr Loop
  -> Ptr Fs
  -> String
  -> (flags,mode : Bits32)
  -> (cb : Ptr Fs -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_open_sync")
prim__uv_fs_open_sync :
     Ptr Loop
  -> Ptr Fs
  -> String
  -> (flags,mode : Bits32)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_read")
prim__uv_fs_read :
     Ptr Loop
  -> Ptr Fs
  -> (file   : Int32)
  -> (bufs   : Ptr Buf)
  -> (nbufs  : Bits32)
  -> (offset : Int32)
  -> (cb     : Ptr Fs -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_write")
prim__uv_fs_write :
     Ptr Loop
  -> Ptr Fs
  -> (file   : Int32)
  -> (bufs   : Ptr Buf)
  -> (nbufs  : Bits32)
  -> (offset : Int64)
  -> (cb     : Ptr Fs -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_write_sync")
prim__uv_fs_write_sync :
     Ptr Loop
  -> (file   : Int32)
  -> (bufs   : Ptr Buf)
  -> (nbufs  : Bits32)
  -> (offset : Int64)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_close")
prim__uv_fs_close :
     Ptr Loop
  -> Ptr Fs
  -> (file : Int32)
  -> (cb   : Ptr Fs -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_close_sync")
prim__uv_fs_close_sync : Ptr Loop -> (file : Int32) -> PrimIO Int32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

parameters {auto has : HasIO io}

  ||| Returns the result code received after a file operation.
  export %inline
  uv_fs_get_result : Ptr Fs -> io Int32
  uv_fs_get_result p = primIO $ prim__uv_fs_get_result p

  ||| Asynchronously closes a file and releases the file handle.
  |||
  ||| Once the file is closed, the given `IO` action is invoked.
  ||| Note: Consider using the synchronous version `uv_fs_close_sync`
  ||| instead for simplicity.
  ||| Closing a file will probably not have a significant blocking effect.
  export %inline
  uv_fs_close : Ptr Loop -> Ptr Fs -> Int32 -> (Ptr Fs -> IO ()) -> io Int32
  uv_fs_close l fs h run = do
    primIO $ prim__uv_fs_close l fs h (\p => toPrim $ run p)

  ||| Synchronously closes a file and releases the file handle.
  export %inline
  uv_fs_close_sync : Ptr Loop -> Int32 -> io Int32
  uv_fs_close_sync l h = primIO $ prim__uv_fs_close_sync l h

  ||| Asynchronously opens a file, invoking the given callback once
  ||| the file is ready.
  export %inline
  uv_fs_open :
       Ptr Loop
    -> Ptr Fs
    -> String
    -> (flags : Bits32)
    -> (mode  : Bits32)
    -> (Ptr Fs -> IO ())
    -> io Int32
  uv_fs_open l ptr path fs m act =
    primIO $ prim__uv_fs_open l ptr path fs m $ \p => toPrim (act p)

  ||| Synchronously opens a file, invoking the given callback once
  ||| the file is ready.
  export %inline
  uv_fs_open_sync :
       Ptr Loop
    -> Ptr Fs
    -> String
    -> (flags : Bits32)
    -> (mode  : Bits32)
    -> io Int32
  uv_fs_open_sync l ptr path fs m =
    primIO $ prim__uv_fs_open_sync l ptr path fs m

  ||| Reads data from a file into the given buffer and invokes
  ||| the callback function once the data is ready.
  |||
  ||| This is a faithful binding to `uv_fs_read`. What you typically want is
  ||| to decide on the return value stored in the `Ptr Fs` you get to figure
  ||| out what to do next. For that, there is `fsRead` as a more convenient
  ||| version.
  export %inline
  uv_fs_read :
       Ptr Loop
    -> Ptr Fs
    -> (file   : Int32)
    -> (bufs   : Ptr Buf)
    -> (nbufs  : Bits32)
    -> (offset : Int32)
    -> (cb     : Ptr Fs -> IO ())
    -> io Int32
  uv_fs_read l f h bufs nbufs offset act =
    primIO $ prim__uv_fs_read l f h bufs nbufs offset $ \fp => toPrim (act fp)

  ||| Writes data from the given buffer to a file and invokes
  ||| the callback function once the data is ready.
  export %inline
  uv_fs_write :
       Ptr Loop
    -> Ptr Fs
    -> (file   : Int32)
    -> (bufs   : Ptr Buf)
    -> (nbufs  : Bits32)
    -> (offset : Int64)
    -> (cb     : Ptr Fs -> IO ())
    -> io Int32
  uv_fs_write l f h bufs nbufs offset act =
    primIO $ prim__uv_fs_write l f h bufs nbufs offset $
      \fp => toPrim (act fp)

  ||| Synchronously writes data from the given buffer to a file and invokes
  ||| the callback function once the data is ready.
  export %inline
  uv_fs_write_sync :
       Ptr Loop
    -> (file   : Int32)
    -> (bufs   : Ptr Buf)
    -> (nbufs  : Bits32)
    -> (offset : Int64)
    -> io Int32
  uv_fs_write_sync l h bufs nbufs offset =
    primIO $ prim__uv_fs_write_sync l h bufs nbufs offset

  export %inline
  uv_fs_req_cleanup : Ptr Fs -> io ()
  uv_fs_req_cleanup fp = primIO $ prim__uv_fs_req_cleanup fp

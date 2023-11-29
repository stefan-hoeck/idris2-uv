module System.UV.Raw.File

import System.UV.Raw.Handle
import System.UV.Raw.Loop
import System.UV.Raw.Pointer
import System.UV.Raw.Util

%default total

export
data UV_Timespec_T : Type where [external]

export
data Stat : Type where

export
data StatFs : Type where

export
data Dir : Type where

export
data Dirent : Type where

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------


export %foreign (idris_uv "uv_get_st_dev")
st_dev : Ptr Stat -> Bits64

export %foreign (idris_uv "uv_get_st_mode")
st_mode : Ptr Stat -> Bits64

export %foreign (idris_uv "uv_get_st_nlink")
st_nlink : Ptr Stat -> Bits64

export %foreign (idris_uv "uv_get_st_uid")
st_uid : Ptr Stat -> Bits64

export %foreign (idris_uv "uv_get_st_gid")
st_gid : Ptr Stat -> Bits64

export %foreign (idris_uv "uv_get_st_rdev")
st_rdev : Ptr Stat -> Bits64

export %foreign (idris_uv "uv_get_st_ino")
st_ino : Ptr Stat -> Bits64

export %foreign (idris_uv "uv_get_st_size")
st_size : Ptr Stat -> Bits64

export %foreign (idris_uv "uv_get_st_blksize")
st_blksize : Ptr Stat -> Bits64

export %foreign (idris_uv "uv_get_st_blocks")
st_blocks : Ptr Stat -> Bits64

export %foreign (idris_uv "uv_get_st_flags")
st_flags : Ptr Stat -> Bits64

export %foreign (idris_uv "uv_get_st_gen")
st_gen : Ptr Stat -> Bits64

export %foreign (idris_uv "uv_get_st_atim")
st_atim : Ptr Stat -> UV_Timespec_T

export %foreign (idris_uv "uv_get_st_mtim")
st_mtim : Ptr Stat -> UV_Timespec_T

export %foreign (idris_uv "uv_get_st_ctim")
st_ctim : Ptr Stat -> UV_Timespec_T

export %foreign (idris_uv "uv_get_f_type")
f_type : Ptr StatFs -> Bits64

export %foreign (idris_uv "uv_get_f_bsize")
f_bsize : Ptr StatFs -> Bits64

export %foreign (idris_uv "uv_get_f_blocks")
f_blocks : Ptr StatFs -> Bits64

export %foreign (idris_uv "uv_get_f_bfree")
f_bfree : Ptr StatFs -> Bits64

export %foreign (idris_uv "uv_get_f_bavail")
f_bavail : Ptr StatFs -> Bits64

export %foreign (idris_uv "uv_get_f_files")
f_files : Ptr StatFs -> Bits64

export %foreign (idris_uv "uv_get_f_ffree")
f_ffree : Ptr StatFs -> Bits64

export %foreign (idris_uv "uv_get_st_birthtim")
st_birthtim : Ptr Stat -> UV_Timespec_T

export %foreign (idris_uv "uv_dirent_unknown")
UV_DIRENT_UNKNOWN : Int32

export %foreign (idris_uv "uv_dirent_file")
UV_DIRENT_FILE : Int32

export %foreign (idris_uv "uv_dirent_dir")
UV_DIRENT_DIR : Int32

export %foreign (idris_uv "uv_dirent_link")
UV_DIRENT_LINK : Int32

export %foreign (idris_uv "uv_dirent_fifo")
UV_DIRENT_FIFO : Int32

export %foreign (idris_uv "uv_dirent_socket")
UV_DIRENT_SOCKET : Int32

export %foreign (idris_uv "uv_dirent_char")
UV_DIRENT_CHAR : Int32

export %foreign (idris_uv "uv_dirent_block")
UV_DIRENT_BLOCK : Int32

export %foreign (idris_uv "uv_fs_get_result")
prim__uv_fs_get_result : Ptr Fs -> PrimIO Int32

%foreign (idris_uv "uv_fs_get_ptr")
prim__uv_fs_get_ptr : Ptr Fs -> PrimIO AnyPtr

%foreign (idris_uv "uv_fs_get_path")
prim__uv_fs_get_path : Ptr Fs -> PrimIO (Ptr Char)

%foreign (idris_uv "uv_fs_get_statbuf")
prim__uv_fs_get_statbuf : Ptr Fs -> PrimIO (Ptr Stat)

%foreign (idris_uv "uv_fs_get_dirent_name")
prim__uv_fs_get_dirent_name : Ptr Dirent -> PrimIO (Ptr Char)

%foreign (idris_uv "uv_fs_get_dirent_type")
prim__uv_fs_get_dirent_type : Ptr Dirent -> PrimIO Int32

%foreign (idris_uv "uv_fs_req_cleanup")
prim__uv_fs_req_cleanup : Ptr Fs -> PrimIO ()

%foreign (idris_uv "uv_fs_unlink")
prim__uv_fs_unlink :
     Ptr Loop
  -> Ptr Fs
  -> String
  -> (Ptr Fs -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_mkdir")
prim__uv_fs_mkdir :
     Ptr Loop
  -> Ptr Fs
  -> String
  -> (mode : Int32)
  -> (Ptr Fs -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_mkdtemp")
prim__uv_fs_mkdtemp :
     Ptr Loop
  -> Ptr Fs
  -> (tpl : String)
  -> (Ptr Fs -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_mkstemp")
prim__uv_fs_mkstemp :
     Ptr Loop
  -> Ptr Fs
  -> (tpl : String)
  -> (Ptr Fs -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_rmdir")
prim__uv_fs_rmdir :
     Ptr Loop
  -> Ptr Fs
  -> (path : String)
  -> (Ptr Fs -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_opendir")
prim__uv_fs_opendir :
     Ptr Loop
  -> Ptr Fs
  -> (path : String)
  -> (Ptr Fs -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_closedir")
prim__uv_fs_closedir :
     Ptr Loop
  -> Ptr Fs
  -> (dir : Ptr Dir)
  -> (Ptr Fs -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_readdir")
prim__uv_fs_readdir :
     Ptr Loop
  -> Ptr Fs
  -> (dir : Ptr Dir)
  -> (Ptr Fs -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_scandir")
prim__uv_fs_scandir :
     Ptr Loop
  -> Ptr Fs
  -> (path : String)
  -> (flags : Int32)
  -> (Ptr Fs -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_scandir_next")
prim__uv_fs_scandir_next : Ptr Fs -> Ptr Dirent -> PrimIO Int32

%foreign (idris_uv "uv_dirents")
prim__uv_dirents : Ptr Dir -> PrimIO (Ptr Dirent)

%foreign (idris_uv "uv_nentries")
prim__uv_nentries : Ptr Dir -> PrimIO Bits32

%foreign (idris_uv "uv_fs_stat")
prim__uv_fs_stat :
     Ptr Loop
  -> Ptr Fs
  -> (path : String)
  -> (Ptr Fs -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_fstat")
prim__uv_fs_fstat :
     Ptr Loop
  -> Ptr Fs
  -> (file : Int32)
  -> (Ptr Fs -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_lstat")
prim__uv_fs_lstat :
     Ptr Loop
  -> Ptr Fs
  -> (path : String)
  -> (Ptr Fs -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_statfs")
prim__uv_fs_statfs :
     Ptr Loop
  -> Ptr Fs
  -> (path : String)
  -> (Ptr Fs -> PrimIO ())
  -> PrimIO Int32

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

  ||| Returns the result of `uv_fs_readlink` and `uv_fs_realpath`
  export %inline
  uv_fs_get_ptr : Ptr Fs -> io AnyPtr
  uv_fs_get_ptr p = primIO $ prim__uv_fs_get_ptr p

  ||| Path affecting the request
  export %inline
  uv_fs_get_path : Ptr Fs -> io (Ptr Char)
  uv_fs_get_path p = primIO (prim__uv_fs_get_path p)

  ||| Returns the result of `uv_fs_stat` and other stat requests.
  export %inline
  uv_fs_get_statbuf : Ptr Fs -> io (Ptr Stat)
  uv_fs_get_statbuf p = primIO $ prim__uv_fs_get_statbuf p

  ||| Equivalent to unlink(2).
  export %inline
  uv_fs_unlink : Ptr Loop -> Ptr Fs -> String -> (Ptr Fs -> IO ()) -> io Int32
  uv_fs_unlink loop fs path cb =
    primIO $ prim__uv_fs_unlink loop fs path (\x => toPrim $ cb x)

  ||| Equivalent to mkdir(2).
  export %inline
  uv_fs_mkdir :
       Ptr Loop
    -> Ptr Fs
    -> String
    -> (mode : Int32)
    -> (Ptr Fs -> IO ())
    -> io Int32
  uv_fs_mkdir loop fs path mode cb =
    primIO $ prim__uv_fs_mkdir loop fs path mode (\x => toPrim $ cb x)

  ||| Equivalent to mkdtemp(3). The result can be found as a null
  ||| terminated string at req->path.
  export %inline
  uv_fs_mkdtemp :
       Ptr Loop
    -> Ptr Fs
    -> (tpl : String)
    -> (Ptr Fs -> IO ())
    -> io Int32
  uv_fs_mkdtemp loop fs tpl cb =
    primIO $ prim__uv_fs_mkdtemp loop fs tpl (\x => toPrim $ cb x)

  ||| Equivalent to mkstemp(3). The result can be found as a null
  ||| terminated string at req->path.
  export %inline
  uv_fs_mkstemp :
       Ptr Loop
    -> Ptr Fs
    -> (tpl : String)
    -> (Ptr Fs -> IO ())
    -> io Int32
  uv_fs_mkstemp loop fs tpl cb =
    primIO $ prim__uv_fs_mkstemp loop fs tpl (\x => toPrim $ cb x)

  ||| Equivalent to rmdir(2).
  export %inline
  uv_fs_rmdir :
       Ptr Loop
    -> Ptr Fs
    -> (path : String)
    -> (Ptr Fs -> IO ())
    -> io Int32
  uv_fs_rmdir loop fs path cb =
    primIO $ prim__uv_fs_rmdir loop fs path (\x => toPrim $ cb x)

  ||| Opens path as a directory stream. On success,
  ||| a uv_dir_t is allocated and returned via req->ptr.
  ||| This memory is not freed by uv_fs_req_cleanup(), although req->ptr
  ||| is set to NULL. The allocated memory must be  freed  by
  ||| calling uv_fs_closedir(). On failure, no memory is allocated.
  |||
  ||| The contents of the directory can be iterated over by passing the
  ||| resulting uv_dir_t to uv_fs_readdir().
  export %inline
  uv_fs_opendir :
       Ptr Loop
    -> Ptr Fs
    -> (path : String)
    -> (Ptr Fs -> IO ())
    -> io Int32
  uv_fs_opendir loop fs path cb =
    primIO $ prim__uv_fs_opendir loop fs path (\x => toPrim $ cb x)

  ||| Closes the directory stream represented by dir and frees the
  ||| memory allocated by `uv_fs_opendir`.
  export %inline
  uv_fs_closedir :
       Ptr Loop
    -> Ptr Fs
    -> (dir : Ptr Dir)
    -> (Ptr Fs -> IO ())
    -> io Int32
  uv_fs_closedir loop fs dir cb =
    primIO $ prim__uv_fs_closedir loop fs dir (\x => toPrim $ cb x)

  ||| Iterates  over  the directory stream, dir, returned by a
  ||| successful `uv_fs_opendir` call. Prior to invoking `uv_fs_readdir`,
  ||| the caller must set dir->dirents and dir->nentries,
  ||| representing the array of uv_dirent_t ele‐
  ||| ments used to hold the read directory entries and its size.
  |||
  ||| On success, the result is an integer >= 0 representing the number
  ||| of entries read from the stream.
  ||| NOTE:
  |||    On success this function allocates memory that must be
  |||    freed using `uv_fs_req_cleanup`. `uv_fs_req_cleanup` must
  |||    be called before closing the directory with `uv_fs_closedir`.
  export %inline
  uv_fs_readdir :
       Ptr Loop
    -> Ptr Fs
    -> (dir : Ptr Dir)
    -> (Ptr Fs -> IO ())
    -> io Int32
  uv_fs_readdir loop fs dir cb =
    primIO $ prim__uv_fs_readdir loop fs dir (\x => toPrim $ cb x)

  ||| Equivalent to scandir(3), with a slightly different API.
  ||| Once the callback for the request is called, the user can use
  ||| `uv_fs_scandir_next` to get ent populated with the next
  ||| directory entry data. When there are no more
  ||| entries UV_EOF will be returned.
  |||
  ||| NOTE:
  |||    Unlike scandir(3), this function does not return the "." and ".." entries.
  |||
  ||| NOTE:
  |||    On Linux, getting the type of an entry is only supported
  |||    by some file systems (btrfs, ext2, ext3 and ext4 at the time of this writing),
  |||    check the getdents(2) man page.
  export %inline
  uv_fs_scandir :
       Ptr Loop
    -> Ptr Fs
    -> (path : String)
    -> (mode : Int32)
    -> (Ptr Fs -> IO ())
    -> io Int32
  uv_fs_scandir loop fs path mode cb =
    primIO $ prim__uv_fs_scandir loop fs path mode (\x => toPrim $ cb x)

  ||| See `uv_fs_scandir`.
  export %inline
  uv_fs_scandir_next : Ptr Fs -> Ptr Dirent -> io Int32
  uv_fs_scandir_next fs ptr = primIO $ prim__uv_fs_scandir_next fs ptr

  export %inline
  uv_dirents : Ptr Dir -> io (Ptr Dirent)
  uv_dirents dir = primIO $ prim__uv_dirents dir

  export %inline
  uv_nentries : Ptr Dir -> io Bits32
  uv_nentries dir = primIO $ prim__uv_nentries dir

  export %inline
  uv_fs_get_dirent_name : Ptr Dirent -> io (Ptr Char)
  uv_fs_get_dirent_name ptr = primIO $ prim__uv_fs_get_dirent_name ptr

  export %inline
  uv_fs_get_dirent_type : Ptr Dirent -> io Int32
  uv_fs_get_dirent_type ptr = primIO $ prim__uv_fs_get_dirent_type ptr

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

  export %inline
  uv_fs_stat :
       Ptr Loop
    -> Ptr Fs
    -> (path : String)
    -> (Ptr Fs -> IO ())
    -> io Int32
  uv_fs_stat loop fs path cb =
    primIO $ prim__uv_fs_stat loop fs path (\p => toPrim $ cb p)

  export %inline
  uv_fs_fstat :
       Ptr Loop
    -> Ptr Fs
    -> (file : Int32)
    -> (Ptr Fs -> IO ())
    -> io Int32
  uv_fs_fstat loop fs file cb =
    primIO $ prim__uv_fs_fstat loop fs file (\p => toPrim $ cb p)

  export %inline
  uv_fs_lstat :
       Ptr Loop
    -> Ptr Fs
    -> (path : String)
    -> (Ptr Fs -> IO ())
    -> io Int32
  uv_fs_lstat loop fs path cb =
    primIO $ prim__uv_fs_lstat loop fs path (\p => toPrim $ cb p)

  ||| Equivalent to statfs(2). On success, a
  ||| `uv_statfs_t` is allocated and returned via req->ptr.
  ||| This memory is freed by `uv_fs_req_cleanup`.
  ||| NOTE:
  |||    Any fields in the resulting uv_statfs_t that are not
  |||    supported by the underlying operating system are set to zero.
  export %inline
  uv_fs_statfs :
       Ptr Loop
    -> Ptr Fs
    -> (path : String)
    -> (Ptr Fs -> IO ())
    -> io Int32
  uv_fs_statfs loop fs path cb =
    primIO $ prim__uv_fs_statfs loop fs path (\p => toPrim $ cb p)


-- Data types
--     type uv_timespec_t
--            Y2K38-unsafe data type for storing times with nanosecond resolution.  Will be replaced with uv_timespec64_t in libuv v2.0.
--
--               typedef struct {
--                   long tv_sec;
--                   long tv_nsec;
--               } uv_timespec_t;
--
--
-- API
--
--     int uv_fs_rename(uv_loop_t *loop, uv_fs_t *req, const char *path, const char *new_path, uv_fs_cb cb)
--            Equivalent to rename(2).
--
--     int uv_fs_fsync(uv_loop_t *loop, uv_fs_t *req, uv_file file, uv_fs_cb cb)
--            Equivalent to fsync(2).
--
--            NOTE:
--               For AIX, uv_fs_fsync returns UV_EBADF on file descriptors referencing non regular files.
--
--     int uv_fs_fdatasync(uv_loop_t *loop, uv_fs_t *req, uv_file file, uv_fs_cb cb)
--            Equivalent to fdatasync(2).
--
--     int uv_fs_ftruncate(uv_loop_t *loop, uv_fs_t *req, uv_file file, int64_t offset, uv_fs_cb cb)
--            Equivalent to ftruncate(2).
--
--     int uv_fs_copyfile(uv_loop_t *loop, uv_fs_t *req, const char *path, const char *new_path, int flags, uv_fs_cb cb)
--            Copies a file from path to new_path. Supported flags are described below.
--
--            • UV_FS_COPYFILE_EXCL: If present, uv_fs_copyfile() will fail with UV_EEXIST if the destination path already exists. The default behavior is to overwrite the destination if it exists.
--
--            • UV_FS_COPYFILE_FICLONE: If present, uv_fs_copyfile() will attempt to create a copy-on-write reflink. If the underlying platform does not support copy-on-write, or an error occurs while attempting to use copy-on-write,
--              a fallback copy mechanism based on uv_fs_sendfile() is used.
--
--            • UV_FS_COPYFILE_FICLONE_FORCE: If present, uv_fs_copyfile() will attempt to create a copy-on-write reflink. If the underlying platform does not support  copy-on-write,  or  an  error  occurs  while  attempting  to  use
--              copy-on-write, then an error is returned.
--
--            WARNING:
--               If  the destination path is created, but an error occurs while copying the data, then the destination path is removed. There is a brief window of time between closing and removing the file where another process could
--               access the file.
--
--            New in version 1.14.0.
--
--            Changed in version 1.20.0: UV_FS_COPYFILE_FICLONE and UV_FS_COPYFILE_FICLONE_FORCE are supported.
--
--            Changed in version 1.33.0: If an error occurs while using UV_FS_COPYFILE_FICLONE_FORCE, that error is returned. Previously, all errors were mapped to UV_ENOTSUP.
--
--     int uv_fs_sendfile(uv_loop_t *loop, uv_fs_t *req, uv_file out_fd, uv_file in_fd, int64_t in_offset, size_t length, uv_fs_cb cb)
--            Limited equivalent to sendfile(2).
--
--     int uv_fs_access(uv_loop_t *loop, uv_fs_t *req, const char *path, int mode, uv_fs_cb cb)
--            Equivalent to access(2) on Unix. Windows uses GetFileAttributesW().
--
--     int uv_fs_chmod(uv_loop_t *loop, uv_fs_t *req, const char *path, int mode, uv_fs_cb cb)
--
--     int uv_fs_fchmod(uv_loop_t *loop, uv_fs_t *req, uv_file file, int mode, uv_fs_cb cb)
--            Equivalent to chmod(2) and fchmod(2) respectively.
--
--     int uv_fs_utime(uv_loop_t *loop, uv_fs_t *req, const char *path, double atime, double mtime, uv_fs_cb cb)
--
--     int uv_fs_futime(uv_loop_t *loop, uv_fs_t *req, uv_file file, double atime, double mtime, uv_fs_cb cb)
--
--     int uv_fs_lutime(uv_loop_t *loop, uv_fs_t *req, const char *path, double atime, double mtime, uv_fs_cb cb)
--            Equivalent to utime(2), futimes(3) and lutimes(3) respectively.
--
--            NOTE:
--               z/OS: uv_fs_lutime() is not implemented for z/OS. It can still be called but will return UV_ENOSYS.
--
--            NOTE:
--               AIX: uv_fs_futime() and uv_fs_lutime() functions only work for AIX 7.1 and newer.  They can still be called on older versions but will return UV_ENOSYS.
--
--            Changed in version 1.10.0: sub-second precission is supported on Windows
--
--     int uv_fs_link(uv_loop_t *loop, uv_fs_t *req, const char *path, const char *new_path, uv_fs_cb cb)
--            Equivalent to link(2).
--
--     int uv_fs_symlink(uv_loop_t *loop, uv_fs_t *req, const char *path, const char *new_path, int flags, uv_fs_cb cb)
--            Equivalent to symlink(2).
--
--            NOTE:
--               On Windows the flags parameter can be specified to control how the symlink will be created:
--
--                   • UV_FS_SYMLINK_DIR: indicates that path points to a directory.
--
--                   • UV_FS_SYMLINK_JUNCTION: request that the symlink is created using junction points.
--
--     int uv_fs_readlink(uv_loop_t *loop, uv_fs_t *req, const char *path, uv_fs_cb cb)
--            Equivalent to readlink(2).  The resulting string is stored in req->ptr.
--
--     int uv_fs_realpath(uv_loop_t *loop, uv_fs_t *req, const char *path, uv_fs_cb cb)
--            Equivalent to realpath(3) on Unix. Windows uses GetFinalPathNameByHandle.  The resulting string is stored in req->ptr.
--
--            WARNING:
--               This function has certain platform-specific caveats that were discovered when used in Node.
--
--               • macOS and other BSDs: this function will fail with UV_ELOOP if more than 32 symlinks are found while resolving the given path.  This limit is hardcoded and cannot be sidestepped.
--
--               • Windows: while this function works in the common case, there are a number of corner cases where it doesn't:
--
--                 • Paths in ramdisk volumes created by tools which sidestep the Volume Manager (such as ImDisk) cannot be resolved.
--
--                 • Inconsistent casing when using drive letters.
--
--                 • Resolved path bypasses subst'd drives.
--
--               While this function can still be used, it's not recommended if scenarios such as the above need to be supported.
--
--               The background story and some more details on these issues can be checked here.
--
--            New in version 1.8.0.
--
--     int uv_fs_chown(uv_loop_t *loop, uv_fs_t *req, const char *path, uv_uid_t uid, uv_gid_t gid, uv_fs_cb cb)
--
--     int uv_fs_fchown(uv_loop_t *loop, uv_fs_t *req, uv_file file, uv_uid_t uid, uv_gid_t gid, uv_fs_cb cb)
--
--     int uv_fs_lchown(uv_loop_t *loop, uv_fs_t *req, const char *path, uv_uid_t uid, uv_gid_t gid, uv_fs_cb cb)
--            Equivalent to chown(2), fchown(2) and lchown(2) respectively.
--
--            NOTE:
--               These functions are not implemented on Windows.
--
--            Changed in version 1.21.0: implemented uv_fs_lchown
--
--     uv_fs_type uv_fs_get_type(const uv_fs_t *req)
--            Returns req->fs_type.
--
--            New in version 1.19.0.
--
--     ssize_t uv_fs_get_result(const uv_fs_t *req)
--            Returns req->result.
--
--            New in version 1.19.0.
--
--     int uv_fs_get_system_error(const uv_fs_t *req)
--            Returns the platform specific error code - GetLastError() value on Windows and -(req->result) on other platforms.
--
--            New in version 1.38.0.
--
--     void *uv_fs_get_ptr(const uv_fs_t *req)
--            Returns req->ptr.
--
--            New in version 1.19.0.
--
--     const char *uv_fs_get_path(const uv_fs_t *req)
--            Returns req->path.
--
--            New in version 1.19.0.
--
--     uv_stat_t *uv_fs_get_statbuf(uv_fs_t *req)
--            Returns &req->statbuf.
--
--            New in version 1.19.0.
--
--     SEE ALSO:
--        The uv_req_t API functions also apply.
--
-- Helper functions
--     uv_os_fd_t uv_get_osfhandle(int fd)
--            For a file descriptor in the C runtime, get the OS-dependent handle.  On UNIX, returns the fd intact. On Windows, this calls _get_osfhandle.  Note that the return value is still owned by the C runtime, any  attempts  to
--            close it or to use it after closing the fd may lead to malfunction.
--               New in version 1.12.0.
--
--     int uv_open_osfhandle(uv_os_fd_t os_fd)
--            For  a OS-dependent handle, get the file descriptor in the C runtime.  On UNIX, returns the os_fd intact. On Windows, this calls _open_osfhandle.  Note that this consumes the argument, any attempts to close it or to use
--            it after closing the return value may lead to malfunction.
--               New in version 1.23.0.
--
-- File open constants
--     UV_FS_O_APPEND
--            The file is opened in append mode. Before each write, the file offset is positioned at the end of the file.
--
--     UV_FS_O_CREAT
--            The file is created if it does not already exist.
--
--     UV_FS_O_DIRECT
--            File I/O is done directly to and from user-space buffers, which must be aligned. Buffer size and address should be a multiple of the physical sector size of the block device.
--
--            NOTE:
--               UV_FS_O_DIRECT is supported on Linux, and on Windows via FILE_FLAG_NO_BUFFERING.  UV_FS_O_DIRECT is not supported on macOS.
--
--     UV_FS_O_DIRECTORY
--            If the path is not a directory, fail the open.
--
--            NOTE:
--               UV_FS_O_DIRECTORY is not supported on Windows.
--
--     UV_FS_O_DSYNC
--            The file is opened for synchronous I/O. Write operations will complete once all data and a minimum of metadata are flushed to disk.
--
--            NOTE:
--               UV_FS_O_DSYNC is supported on Windows via FILE_FLAG_WRITE_THROUGH.
--
--     UV_FS_O_EXCL
--            If the O_CREAT flag is set and the file already exists, fail the open.
--
--            NOTE:
--               In general, the behavior of O_EXCL is undefined if it is used without O_CREAT. There is one exception: on Linux 2.6 and later, O_EXCL can be used without O_CREAT if pathname refers to a block device. If the block de‐
--               vice is in use by the system (e.g., mounted), the open will fail with the error EBUSY.
--
--     UV_FS_O_EXLOCK
--            Atomically obtain an exclusive lock.
--
--            NOTE:
--               UV_FS_O_EXLOCK is only supported on macOS and Windows.
--
--            Changed in version 1.17.0: support is added for Windows.
--
--     UV_FS_O_FILEMAP
--            Use a memory file mapping to access the file. When using this flag, the file cannot be open multiple times concurrently.
--
--            NOTE:
--               UV_FS_O_FILEMAP is only supported on Windows.
--
--     UV_FS_O_NOATIME
--            Do not update the file access time when the file is read.
--
--            NOTE:
--               UV_FS_O_NOATIME is not supported on Windows.
--
--     UV_FS_O_NOCTTY
--            If the path identifies a terminal device, opening the path will not cause that terminal to become the controlling terminal for the process (if the process does not already have one).
--
--            NOTE:
--               UV_FS_O_NOCTTY is not supported on Windows.
--
--     UV_FS_O_NOFOLLOW
--            If the path is a symbolic link, fail the open.
--
--            NOTE:
--               UV_FS_O_NOFOLLOW is not supported on Windows.
--
--     UV_FS_O_NONBLOCK
--            Open the file in nonblocking mode if possible.
--
--            NOTE:
--               UV_FS_O_NONBLOCK is not supported on Windows.
--
--     UV_FS_O_RANDOM
--            Access is intended to be random. The system can use this as a hint to optimize file caching.
--
--            NOTE:
--               UV_FS_O_RANDOM is only supported on Windows via FILE_FLAG_RANDOM_ACCESS.
--
--     UV_FS_O_RDONLY
--            Open the file for read-only access.
--
--     UV_FS_O_RDWR
--            Open the file for read-write access.
--
--     UV_FS_O_SEQUENTIAL
--            Access is intended to be sequential from beginning to end. The system can use this as a hint to optimize file caching.
--
--            NOTE:
--               UV_FS_O_SEQUENTIAL is only supported on Windows via FILE_FLAG_SEQUENTIAL_SCAN.
--
--     UV_FS_O_SHORT_LIVED
--            The file is temporary and should not be flushed to disk if possible.
--
--            NOTE:
--               UV_FS_O_SHORT_LIVED is only supported on Windows via FILE_ATTRIBUTE_TEMPORARY.
--
--     UV_FS_O_SYMLINK
--            Open the symbolic link itself rather than the resource it points to.
--
--     UV_FS_O_SYNC
--            The file is opened for synchronous I/O. Write operations will complete once all data and all metadata are flushed to disk.
--
--            NOTE:
--               UV_FS_O_SYNC is supported on Windows via FILE_FLAG_WRITE_THROUGH.
--
--     UV_FS_O_TEMPORARY
--            The file is temporary and should not be flushed to disk if possible.
--
--            NOTE:
--               UV_FS_O_TEMPORARY is only supported on Windows via FILE_ATTRIBUTE_TEMPORARY.
--
--     UV_FS_O_TRUNC
--            If the file exists and is a regular file, and the file is opened successfully for write access, its length shall be truncated to zero.
--
--     UV_FS_O_WRONLY
--            Open the file for write-only access.

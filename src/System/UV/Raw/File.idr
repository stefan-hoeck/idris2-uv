module System.UV.Raw.File

import System.UV.Raw.Callback
import System.UV.Raw.Handle
import System.UV.Raw.Loop
import System.UV.Raw.Pointer
import System.UV.Raw.Req
import System.UV.Raw.Util

import public System.UV.Data.File

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

||| Alias for a foreign callable code object
public export
0 FsCB : Type
FsCB = AnyPtr

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

export %foreign (idris_uv "uv_get_st_birthtim")
st_birthtim : Ptr Stat -> UV_Timespec_T

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

export %foreign (idris_uv "uv_get_tv_sec")
tv_sec : UV_Timespec_T -> Int64

export %foreign (idris_uv "uv_get_tv_nsec")
tv_nsec : UV_Timespec_T -> Int64

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
  -> AnyPtr
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_mkdir")
prim__uv_fs_mkdir :
     Ptr Loop
  -> Ptr Fs
  -> String
  -> (mode : Int32)
  -> AnyPtr
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_mkdtemp")
prim__uv_fs_mkdtemp :
     Ptr Loop
  -> Ptr Fs
  -> (tpl : String)
  -> AnyPtr
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_mkstemp")
prim__uv_fs_mkstemp :
     Ptr Loop
  -> Ptr Fs
  -> (tpl : String)
  -> AnyPtr
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_rmdir")
prim__uv_fs_rmdir :
     Ptr Loop
  -> Ptr Fs
  -> (path : String)
  -> AnyPtr
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_opendir")
prim__uv_fs_opendir :
     Ptr Loop
  -> Ptr Fs
  -> (path : String)
  -> AnyPtr
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_closedir")
prim__uv_fs_closedir :
     Ptr Loop
  -> Ptr Fs
  -> (dir : Ptr Dir)
  -> AnyPtr
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_readdir")
prim__uv_fs_readdir :
     Ptr Loop
  -> Ptr Fs
  -> (dir : Ptr Dir)
  -> AnyPtr
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_scandir")
prim__uv_fs_scandir :
     Ptr Loop
  -> Ptr Fs
  -> (path : String)
  -> (flags : Int32)
  -> AnyPtr
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
  -> AnyPtr
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_fstat")
prim__uv_fs_fstat :
     Ptr Loop
  -> Ptr Fs
  -> (file : Int32)
  -> AnyPtr
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_lstat")
prim__uv_fs_lstat :
     Ptr Loop
  -> Ptr Fs
  -> (path : String)
  -> AnyPtr
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_statfs")
prim__uv_fs_statfs :
     Ptr Loop
  -> Ptr Fs
  -> (path : String)
  -> AnyPtr
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_open")
prim__uv_fs_open :
     Ptr Loop
  -> Ptr Fs
  -> String
  -> (flags,mode : Bits32)
  -> (cb : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "idris_uv_fs_read")
prim__uv_fs_read :
     Ptr Loop
  -> Ptr Fs
  -> (file   : Int32)
  -> (buf    : Ptr Bits8)
  -> (size   : Bits32)
  -> (offset : Int64)
  -> (cb     : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "idris_uv_fs_write")
prim__uv_fs_write :
     Ptr Loop
  -> Ptr Fs
  -> (file   : Int32)
  -> (buf    : Ptr Bits8)
  -> (size   : Bits32)
  -> (offset : Int64)
  -> (cb     : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_close")
prim__uv_fs_close :
     Ptr Loop
  -> Ptr Fs
  -> (file : Int32)
  -> (cb   : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_rename")
prim__uv_fs_rename :
     Ptr Loop
  -> Ptr Fs
  -> (path, newpath : String)
  -> (cb   : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_fsync")
prim__uv_fs_fsync :
     Ptr Loop
  -> Ptr Fs
  -> (file : Int32)
  -> (cb   : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_fdatasync")
prim__uv_fs_fdatasync :
     Ptr Loop
  -> Ptr Fs
  -> (file : Int32)
  -> (cb   : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_fdatasync")
prim__uv_fs_ftruncate :
     Ptr Loop
  -> Ptr Fs
  -> (file : Int32)
  -> (offset : Int64)
  -> (cb   : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_fdatasync")
prim__uv_fs_copyfile :
     Ptr Loop
  -> Ptr Fs
  -> (path, newpath : String)
  -> (flags : Int32)
  -> (cb   : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_sendfile")
prim__uv_fs_sendfile :
     Ptr Loop
  -> Ptr Fs
  -> (outFile, inFile : Int32)
  -> (offset : Int64)
  -> (length : Bits32)
  -> (cb   : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_access")
prim__uv_fs_access :
     Ptr Loop
  -> Ptr Fs
  -> (path : String)
  -> (mode : Int32)
  -> (cb   : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_chmod")
prim__uv_fs_chmod :
     Ptr Loop
  -> Ptr Fs
  -> (path : String)
  -> (mode : Int32)
  -> (cb   : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_fchmod")
prim__uv_fs_fchmod :
     Ptr Loop
  -> Ptr Fs
  -> (file : Int32)
  -> (mode : Int32)
  -> (cb   : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_utime")
prim__uv_fs_utime :
     Ptr Loop
  -> Ptr Fs
  -> (path : String)
  -> (atime, mtime : Double)
  -> (cb   : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_futime")
prim__uv_fs_futime :
     Ptr Loop
  -> Ptr Fs
  -> (file : Int32)
  -> (atime, mtime : Double)
  -> (cb   : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_lutime")
prim__uv_fs_lutime :
     Ptr Loop
  -> Ptr Fs
  -> (path : String)
  -> (atime, mtime : Double)
  -> (cb   : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_link")
prim__uv_fs_link :
     Ptr Loop
  -> Ptr Fs
  -> (path, newpath : String)
  -> (cb   : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_symlink")
prim__uv_fs_symlink :
     Ptr Loop
  -> Ptr Fs
  -> (path, newpath : String)
  -> (flags : Int32)
  -> (cb   : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_readlink")
prim__uv_fs_readlink :
     Ptr Loop
  -> Ptr Fs
  -> (path : String)
  -> (cb   : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_realpath")
prim__uv_fs_realpath :
     Ptr Loop
  -> Ptr Fs
  -> (path : String)
  -> (cb   : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_chown")
prim__uv_fs_chown :
     Ptr Loop
  -> Ptr Fs
  -> (path : String)
  -> (uid, gid : Int32)
  -> (cb   : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_fchown")
prim__uv_fs_fchown :
     Ptr Loop
  -> Ptr Fs
  -> (file : String)
  -> (uid, gid : Int32)
  -> (cb   : AnyPtr)
  -> PrimIO Int32

%foreign (idris_uv "uv_fs_lchown")
prim__uv_fs_lchown :
     Ptr Loop
  -> Ptr Fs
  -> (path : String)
  -> (uid, gid : Int32)
  -> (cb   : AnyPtr)
  -> PrimIO Int32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

export %inline
uv_fs_req_cleanup : HasIO io => Ptr Fs -> io ()
uv_fs_req_cleanup fp = primIO $ prim__uv_fs_req_cleanup fp

parameters {auto has : HasIO io}

  localCB : (Ptr Fs -> IO ()) -> io FsCB
  localCB f =
    ptrCB $ \p => do
      f p
      uv_fs_req_cleanup p
      freeReq p

  ||| Synchronously run a file system request.
  export
  sync : (Ptr Fs -> FsCB -> io a) -> io a
  sync f = do
    fs <- mallocPtr Fs
    res <- f fs prim__getNullAnyPtr
    freePtr fs
    pure res

  ||| Asynchronously run a file system request.
  export
  async : (Ptr Fs -> FsCB -> io a) -> (Ptr Fs -> IO ()) -> io a
  async f cb = do
    fscb <- localCB cb
    p    <- mallocPtr Fs
    uv_req_set_data p fscb
    f p fscb

  ||| Asynchronously run a file system request without running a
  ||| a custom callback.
  export %inline
  async' : (Ptr Fs -> FsCB -> io a) -> io a
  async' f = async f (\_ => pure ())

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
  uv_fs_unlink : Ptr Loop -> Ptr Fs -> String -> FsCB -> io Int32
  uv_fs_unlink loop fs path cb =
    primIO $ prim__uv_fs_unlink loop fs path cb

  ||| Equivalent to mkdir(2).
  export %inline
  uv_fs_mkdir :
       Ptr Loop
    -> String
    -> (mode : Int32)
    -> Ptr Fs
    -> FsCB
    -> io Int32
  uv_fs_mkdir loop path mode fs cb =
    primIO $ prim__uv_fs_mkdir loop fs path mode cb

  ||| Equivalent to mkdtemp(3). The result can be found as a null
  ||| terminated string at req->path.
  export %inline
  uv_fs_mkdtemp :
       Ptr Loop
    -> (tpl : String)
    -> Ptr Fs
    -> FsCB
    -> io Int32
  uv_fs_mkdtemp loop tpl fs cb =
    primIO $ prim__uv_fs_mkdtemp loop fs tpl cb

  ||| Equivalent to mkstemp(3). The result can be found as a null
  ||| terminated string at req->path.
  export %inline
  uv_fs_mkstemp :
       Ptr Loop
    -> (tpl : String)
    -> Ptr Fs
    -> FsCB
    -> io Int32
  uv_fs_mkstemp loop tpl fs cb =
    primIO $ prim__uv_fs_mkstemp loop fs tpl cb

  ||| Equivalent to rmdir(2).
  export %inline
  uv_fs_rmdir :
       Ptr Loop
    -> (path : String)
    -> Ptr Fs
    -> FsCB
    -> io Int32
  uv_fs_rmdir loop path fs cb =
    primIO $ prim__uv_fs_rmdir loop fs path cb

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
    -> (path : String)
    -> Ptr Fs
    -> FsCB
    -> io Int32
  uv_fs_opendir loop path fs cb =
    primIO $ prim__uv_fs_opendir loop fs path cb

  ||| Closes the directory stream represented by dir and frees the
  ||| memory allocated by `uv_fs_opendir`.
  export %inline
  uv_fs_closedir :
       Ptr Loop
    -> (dir : Ptr Dir)
    -> Ptr Fs
    -> FsCB
    -> io Int32
  uv_fs_closedir loop dir fs cb =
    primIO $ prim__uv_fs_closedir loop fs dir cb

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
    -> (dir : Ptr Dir)
    -> Ptr Fs
    -> FsCB
    -> io Int32
  uv_fs_readdir loop dir fs cb =
    primIO $ prim__uv_fs_readdir loop fs dir cb

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
    -> (path : String)
    -> (mode : Int32)
    -> Ptr Fs
    -> FsCB
    -> io Int32
  uv_fs_scandir loop path mode fs cb =
    primIO $ prim__uv_fs_scandir loop fs path mode cb

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
  export %inline
  uv_fs_close : Ptr Loop -> Int32 -> Ptr Fs -> FsCB -> io Int32
  uv_fs_close l h fs cb = do
    primIO $ prim__uv_fs_close l fs h cb

  ||| Asynchronously opens a file, invoking the given callback once
  ||| the file is ready.
  export %inline
  uv_fs_open :
       Ptr Loop
    -> String
    -> (flags : Bits32)
    -> (mode  : Bits32)
    -> Ptr Fs
    -> FsCB
    -> io Int32
  uv_fs_open l path fs m ptr cb =
    primIO $ prim__uv_fs_open l ptr path fs m cb

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
    -> (file   : Int32)
    -> (buf    : Ptr Bits8)
    -> (size   : Bits32)
    -> (offset : Int64)
    -> Ptr Fs
    -> (cb     : FsCB)
    -> io Int32
  uv_fs_read l h buf size offset f cb =
    primIO $ prim__uv_fs_read l f h buf size offset cb

  ||| Writes data from the given buffer to a file and invokes
  ||| the callback function once the data is ready.
  export
  uv_fs_write :
       Ptr Loop
    -> (file   : Int32)
    -> (buf    : Ptr Bits8)
    -> (size   : Bits32)
    -> (offset : Int64)
    -> (p      : Ptr Fs)
    -> (cb     : FsCB)
    -> io Int32
  uv_fs_write l h buf size offset p cb =
    primIO $ prim__uv_fs_write l p h buf size offset cb

  export %inline
  uv_fs_stat :
       Ptr Loop
    -> (path : String)
    -> Ptr Fs
    -> FsCB
    -> io Int32
  uv_fs_stat loop path fs cb =
    primIO $ prim__uv_fs_stat loop fs path cb

  export %inline
  uv_fs_fstat :
       Ptr Loop
    -> (file : Int32)
    -> Ptr Fs
    -> FsCB
    -> io Int32
  uv_fs_fstat loop file fs cb =
    primIO $ prim__uv_fs_fstat loop fs file cb

  export %inline
  uv_fs_lstat :
       Ptr Loop
    -> (path : String)
    -> Ptr Fs
    -> FsCB
    -> io Int32
  uv_fs_lstat loop path fs cb =
    primIO $ prim__uv_fs_lstat loop fs path cb

  ||| Equivalent to statfs(2). On success, a
  ||| `uv_statfs_t` is allocated and returned via req->ptr.
  ||| This memory is freed by `uv_fs_req_cleanup`.
  ||| NOTE:
  |||    Any fields in the resulting uv_statfs_t that are not
  |||    supported by the underlying operating system are set to zero.
  export %inline
  uv_fs_statfs :
       Ptr Loop
    -> (path : String)
    -> Ptr Fs
    -> FsCB
    -> io Int32
  uv_fs_statfs loop path fs cb =
    primIO $ prim__uv_fs_statfs loop fs path cb

  ||| Equivalent to rename(2).
  export %inline
  uv_fs_rename :
       Ptr Loop
    -> (path, newpath : String)
    -> Ptr Fs
    -> (cb   : FsCB)
    -> io Int32
  uv_fs_rename loop path newpath fs cb =
    primIO $ prim__uv_fs_rename loop fs path newpath cb

  ||| Equivalent to fsync(2).
  |||
  ||| NOTE:
  |||    For AIX, uv_fs_fsync returns UV_EBADF on file
  |||    descriptors referencing non regular files.
  export %inline
  uv_fs_fsync :
       Ptr Loop
    -> (file : Int32)
    -> Ptr Fs
    -> (cb   : FsCB)
    -> io Int32
  uv_fs_fsync loop file fs cb =
    primIO $ prim__uv_fs_fsync loop fs file cb

  ||| Equivalent to fdatasync(2).
  export %inline
  uv_fs_fdatasync :
       Ptr Loop
    -> (file : Int32)
    -> Ptr Fs
    -> (cb   : FsCB)
    -> io Int32
  uv_fs_fdatasync loop file fs cb =
    primIO $ prim__uv_fs_fdatasync loop fs file cb

  ||| Equivalent to ftruncate(2).
  export %inline
  uv_fs_ftruncate :
       Ptr Loop
    -> (file : Int32)
    -> (offset : Int64)
    -> Ptr Fs
    -> (cb   : FsCB)
    -> io Int32
  uv_fs_ftruncate loop file offset fs cb =
    primIO $ prim__uv_fs_ftruncate loop fs file offset cb

  ||| Copies a file from path to new_path.
  ||| Supported flags are described below.
  |||
  ||| • UV_FS_COPYFILE_EXCL: If present, `uv_fs_copyfile` will fail
  |||   with UV_EEXIST if the destination path already exists.
  |||   The default behavior is to overwrite the destination if it exists.
  |||
  ||| • UV_FS_COPYFILE_FICLONE: If present, `uv_fs_copyfile` will
  |||   attempt to create a copy-on-write reflink. If the underlying
  |||   platform does not support copy-on-write, or an error occurs
  |||   while attempting to use copy-on-write,
  |||   a fallback copy mechanism based on uv_fs_sendfile() is used.
  |||
  ||| • UV_FS_COPYFILE_FICLONE_FORCE: If present, `uv_fs_copyfile`
  |||   will attempt to create a copy-on-write reflink. If the
  |||   underlying platform does not support  copy-on-write, or an error
  |||   occurs while attempting to use copy-on-write, then an error is returned.
  |||
  ||| WARNING:
  |||    If  the destination path is created, but an error occurs while copying
  |||    the data, then the destination path is removed. There is a brief
  |||    window of time between closing and removing the file where
  |||    another process could access the file.
  export %inline
  uv_fs_copyfile :
       Ptr Loop
    -> (path, newpath : String)
    -> (flags : Int32)
    -> Ptr Fs
    -> (cb   : FsCB)
    -> io Int32
  uv_fs_copyfile loop path newpath flags fs cb =
    primIO $ prim__uv_fs_copyfile loop fs path newpath flags cb

  ||| Limited equivalent to sendfile(2).
  export %inline
  uv_fs_sendfile :
       Ptr Loop
    -> (outFile, inFile : Int32)
    -> (offset : Int64)
    -> (length : Bits32)
    -> Ptr Fs
    -> (cb   : FsCB)
    -> io Int32
  uv_fs_sendfile loop o i offset l fs cb =
    primIO $ prim__uv_fs_sendfile loop fs o i offset l cb

  ||| Equivalent to access(2) on Unix. Windows uses GetFileAttributesW().
  export %inline
  uv_fs_access :
       Ptr Loop
    -> (path : String)
    -> (mode : Int32)
    -> Ptr Fs
    -> (cb   : FsCB)
    -> io Int32
  uv_fs_access loop path mode fs cb =
    primIO $ prim__uv_fs_access loop fs path mode cb

  ||| Equivalent to chmod(2) respectively.
  export %inline
  uv_fs_chmod :
       Ptr Loop
    -> (path : String)
    -> (mode : Int32)
    -> Ptr Fs
    -> (cb   : FsCB)
    -> io Int32
  uv_fs_chmod loop path mode fs cb =
    primIO $ prim__uv_fs_chmod loop fs path mode cb

  ||| Equivalent to fchmod(2) respectively.
  export %inline
  uv_fs_fchmod :
       Ptr Loop
    -> (file : Int32)
    -> (mode : Int32)
    -> Ptr Fs
    -> (cb   : FsCB)
    -> io Int32
  uv_fs_fchmod loop file mode fs cb =
    primIO $ prim__uv_fs_fchmod loop fs file mode cb

  ||| Equivalent to utime(2).
  export %inline
  uv_fs_utime :
       Ptr Loop
    -> (path : String)
    -> (atime, mtime : Double)
    -> Ptr Fs
    -> (cb   : FsCB)
    -> io Int32
  uv_fs_utime loop path atime mtime fs cb =
    primIO $ prim__uv_fs_utime loop fs path atime mtime cb

  ||| Equivalent to futime(2).
  export %inline
  uv_fs_futime :
       Ptr Loop
    -> (file : Int32)
    -> (atime, mtime : Double)
    -> Ptr Fs
    -> (cb   : FsCB)
    -> io Int32
  uv_fs_futime loop file atime mtime fs cb =
    primIO $ prim__uv_fs_futime loop fs file atime mtime cb

  ||| Equivalent to lutime(2).
  export %inline
  uv_fs_lutime :
       Ptr Loop
    -> (path : String)
    -> (atime, mtime : Double)
    -> Ptr Fs
    -> (cb   : FsCB)
    -> io Int32
  uv_fs_lutime loop path atime mtime fs cb =
    primIO $ prim__uv_fs_lutime loop fs path atime mtime cb

  ||| Equivalent to link(2).
  export %inline
  uv_fs_link :
       Ptr Loop
    -> (path, newpath : String)
    -> Ptr Fs
    -> (cb   : FsCB)
    -> io Int32
  uv_fs_link loop path newpath fs cb =
    primIO $ prim__uv_fs_link loop fs path newpath cb

  ||| Equivalent to symlink(2).
  |||
  ||| NOTE:
  |||    On Windows the flags parameter can be specified to control
  |||    how the symlink will be created:
  |||
  |||    • UV_FS_SYMLINK_DIR: indicates that path points to a directory.
  |||
  |||    • UV_FS_SYMLINK_JUNCTION: request that the symlink is
  |||      created using junction points.
  export %inline
  uv_fs_symlink :
       Ptr Loop
    -> (path, newpath : String)
    -> (flags : Int32)
    -> Ptr Fs
    -> (cb   : FsCB)
    -> io Int32
  uv_fs_symlink loop path newpath flags fs cb =
    primIO $ prim__uv_fs_symlink loop fs path newpath flags cb

  ||| Equivalent to readlink(2).  The resulting string is stored in req->ptr.
  export %inline
  uv_fs_readlink :
       Ptr Loop
    -> (path : String)
    -> Ptr Fs
    -> (cb   : FsCB)
    -> io Int32
  uv_fs_readlink loop path fs cb =
    primIO $ prim__uv_fs_readlink loop fs path cb

  ||| Equivalent to realpath(3) on Unix. Windows uses
  ||| GetFinalPathNameByHandle. The resulting string is stored in req->ptr.
  |||
  ||| WARNING:
  |||    This function has certain platform-specific caveats that
  |||    were discovered when used in Node.
  |||
  |||    • macOS and other BSDs: this function will fail with UV_ELOOP if
  |||      more than 32 symlinks are found while resolving the given path.
  |||      This limit is hardcoded and cannot be sidestepped.
  |||
  |||    • Windows: while this function works in the common case,
  |||      there are a number of corner cases where it doesn't:
  |||
  |||      • Paths in ramdisk volumes created by tools which sidestep the
  |||        Volume Manager (such as ImDisk) cannot be resolved.
  |||
  |||      • Inconsistent casing when using drive letters.
  |||
  |||      • Resolved path bypasses subst'd drives.
  |||
  |||    While this function can still be used, it's not recommended
  |||    if scenarios such as the above need to be supported.
  export %inline
  uv_fs_realpath :
       Ptr Loop
    -> (path : String)
    -> Ptr Fs
    -> (cb   : FsCB)
    -> io Int32
  uv_fs_realpath loop path fs cb =
    primIO $ prim__uv_fs_realpath loop fs path cb

  ||| Equivalent to chown(2).
  export %inline
  uv_fs_chown :
       Ptr Loop
    -> (path : String)
    -> (uid, gid : Int32)
    -> Ptr Fs
    -> (cb   : FsCB)
    -> io Int32
  uv_fs_chown loop path uid gid fs cb =
    primIO $ prim__uv_fs_chown loop fs path uid gid cb

  ||| Equivalent to fchown(2).
  export %inline
  uv_fs_fchown :
       Ptr Loop
    -> (file : String)
    -> (uid, gid : Int32)
    -> Ptr Fs
    -> (cb   : FsCB)
    -> io Int32
  uv_fs_fchown loop file uid gid fs cb =
    primIO $ prim__uv_fs_lchown loop fs file uid gid cb

  ||| Equivalent to lchown(2).
  export %inline
  uv_fs_lchown :
       Ptr Loop
    -> (path : String)
    -> (uid, gid : Int32)
    -> Ptr Fs
    -> (cb   : FsCB)
    -> io Int32
  uv_fs_lchown loop path uid gid fs cb =
    primIO $ prim__uv_fs_lchown loop fs path uid gid cb

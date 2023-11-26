module System.UV.File

import Data.Buffer.Indexed
import Data.ByteString
import Data.Buffer
import System.UV.Error
import System.UV.File.Flags
import System.UV.Handle
import System.UV.Loop
import System.UV.Pointer
import System.UV.Util
import public System.UV.Raw.File

%default total

||| A file handle.
public export
record File where
  constructor MkFile
  file : Int32

||| File handle for standard input
export %inline
stdin : File
stdin = MkFile 0

||| File handle for standard output
export %inline
stdout : File
stdout = MkFile 1

||| File handle for standard err
export %inline
stderr : File
stderr = MkFile 2

export
releaseFs : HasIO io => Ptr Fs -> io ()
releaseFs p = uv_fs_req_cleanup p >> freePtr p

withFile : (Either UVError File -> IO ()) -> Ptr Fs -> IO ()
withFile act p = do
  n <- uv_fs_get_result p
  releaseFs p
  if n < 0 then act (Left $ fromCode n) else act (Right $ MkFile n)

||| Asynchronously opens a file, invoking the given callback once
||| the file is ready.
export %inline
fsOpen :
     {auto l : Loop}
  -> String
  -> Flags
  -> Mode
  -> (Either UVError File -> IO ())
  -> UVIO ()
fsOpen path f m act = do
  fs <- mallocPtr Fs
  uvio $ uv_fs_open l.loop fs path f.flags m.mode (withFile act)

export %inline
fsClose : HasIO io => (l : Loop) => File -> io ()
fsClose f = ignore $ uv_fs_close_sync l.loop f.file

--------------------------------------------------------------------------------
-- File Reading
--------------------------------------------------------------------------------

public export
data ReadRes : (a : Type) -> Type where
  Err    : UVError -> ReadRes s
  NoData : ReadRes a
  Data   : a -> ReadRes a

export
Functor ReadRes where
  map f (Err e)  = Err e
  map f NoData   = NoData
  map f (Data v) = Data $ f v

export
Foldable ReadRes where
  foldl acc v (Err e)  = v
  foldl acc v NoData   = v
  foldl acc v (Data x) = acc v x

  foldr acc v (Err e)  = v
  foldr acc v NoData   = v
  foldr acc v (Data x) = acc x v

  foldMap f (Err e)  = neutral
  foldMap f NoData   = neutral
  foldMap f (Data x) = f x

  toList (Err e)  = []
  toList NoData   = []
  toList (Data x) = [x]

export
Traversable ReadRes where
  traverse f (Err e)  = pure $ Err e
  traverse f NoData   = pure NoData
  traverse f (Data x) = Data <$> f x

export
codeToRes : Int32 -> ReadRes Bits32
codeToRes 0 = NoData
codeToRes n = if n < 0 then Err (fromCode n) else Data (cast n)

readRes : HasIO io => Ptr Buf -> Ptr Fs -> io (ReadRes ByteString)
readRes buf fs = do
  c <- uv_fs_get_result fs
  traverse (toByteString buf) (codeToRes c)

readAndReleaseRes : HasIO io => Ptr Buf -> Ptr Fs -> io (ReadRes ByteString)
readAndReleaseRes buf fs = do
  res <- readRes buf fs
  freeBuf buf
  releaseFs fs
  pure res

||| Asynchronously reads up to the given number of bytes from the given file.
export
fsReadBytes :
     {auto l : Loop}
  -> (file   : File)
  -> (bytes  : Bits32)
  -> (cb     : ReadRes ByteString -> IO ())
  -> IO ()
fsReadBytes f bytes cb = do
  fr  <- mallocPtr Fs
  buf <- mallocBuf bytes
  res <- uv_fs_read l.loop fr f.file buf 1 (-1) $ \fr =>
    readAndReleaseRes buf fr >>= cb
  case uvRes res of
    Left err => freeBuf buf >> releaseFs fr >> cb (Err err)
    _        => pure ()

||| Tries to open the given file and to
||| asynchronously read up to the given number of bytes.
export
readBytes :
     {auto l : Loop}
  -> (path   : String)
  -> (bytes  : Bits32)
  -> (cb     : ReadRes ByteString -> IO ())
  -> UVIO ()
readBytes path bytes cb =
  fsOpen path RDONLY neutral $
    \case Left err => cb (Err err)
          Right f  => fsReadBytes f bytes (\r => fsClose f >> cb r)

||| Tries to open the given file and to
||| asynchronously read up to the given number of bytes.
|||
||| The data read is interpreted as a UTF8-encoded string.
export %inline
readText :
     {auto l : Loop}
  -> (path   : String)
  -> (bytes  : Bits32)
  -> (cb     : ReadRes String -> IO ())
  -> UVIO ()
readText path bytes cb =
  readBytes path bytes (cb . map toString)

--------------------------------------------------------------------------------
-- File Writing
--------------------------------------------------------------------------------

export
fsWriteBytesFrom :
     {auto has : HasIO io}
  -> {auto l : Loop}
  -> File
  -> ByteString
  -> (offset : Int64)
  -> (onErr : UVError -> IO ())
  -> io ()
fsWriteBytesFrom f dat offset onErr = do
  buf <- fromByteString dat
  res <- uv_fs_write_sync l.loop f.file buf 1 offset
  freeBuf buf
  liftIO $ traverse_ onErr (toErr res)

export %inline
fsWriteBytes :
     {auto has : HasIO io}
  -> {auto l : Loop}
  -> File
  -> ByteString
  -> (onErr : UVError -> IO ())
  -> io ()
fsWriteBytes f dat onErr = fsWriteBytesFrom f dat (-1) onErr

export
fsWrite :
     {auto l : Loop}
  -> (path : String)
  -> ByteString
  -> (onErr : UVError -> IO ())
  -> UVIO ()
fsWrite path dat onErr = do
  fsOpen path (WRONLY <+> CREAT) neutral $
    \case Left err => pure ()
          Right f  => fsWriteBytes f dat onErr >> fsClose f

export
putOut : Loop => HasIO io => String -> io ()
putOut s = fsWriteBytes stdout (fromString s) (const $ pure ())

export %inline
putOutLn : Loop => HasIO io => String -> io ()
putOutLn s = putOut (s ++ "\n")

export %inline
printOut : Loop => HasIO io => Show a => a -> io ()
printOut = putOut . show

export %inline
printOutLn : Loop => HasIO io => String -> io ()
printOutLn = putOutLn . show

export
putErr : Loop => HasIO io => String -> io ()
putErr s = fsWriteBytes stderr (fromString s) (const $ pure ())

export %inline
putErrLn : Loop => HasIO io => String -> io ()
putErrLn s = putErr (s ++ "\n")

export %inline
printErr : Loop => HasIO io => Show a => a -> io ()
printErr = putErr . show

export %inline
printErrLn : Loop => HasIO io => String -> io ()
printErrLn = putErrLn . show

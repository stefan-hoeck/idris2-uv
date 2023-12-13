module System.UV.File

import System.Rx
import Data.IORef
import Data.Buffer.Indexed
import Data.ByteString
import Data.Buffer
import System.UV.Error
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

export %inline
fsClose : HasIO io => (l : UVLoop) => File -> io ()
fsClose f = ignore $ uv_fs_close_sync l.loop f.file

withFile : UVLoop => (Either UVError (IO (), File) -> IO ()) -> Ptr Fs -> IO ()
withFile act p = do
  n <- uv_fs_get_result p
  releaseFs p
  if n < 0
     then act (Left $ fromCode n)
     else let f := MkFile n in act (Right (fsClose f, f))

||| Asynchronously opens a file, invoking the given callback once
||| the file is ready.
export %inline
fsOpen :
     {auto l : UVLoop}
  -> String
  -> Flags
  -> Mode
  -> (Either UVError (IO (), File) -> IO ())
  -> IO ()
fsOpen path f m act = do
  fs  <- mallocPtr Fs
  res <- uv_fs_open l.loop fs path f.flags m.mode (withFile act)
  case uvRes res of
    Left err => act (Left err) >> releaseFs fs
    Right _  => pure ()

-- --------------------------------------------------------------------------------
-- -- File Reading
-- --------------------------------------------------------------------------------
--
-- public export
-- data ReadRes : (a : Type) -> Type where
--   Err    : UVError -> ReadRes s
--   NoData : ReadRes a
--   Data   : a -> ReadRes a
--
-- export
-- Functor ReadRes where
--   map f (Err e)  = Err e
--   map f NoData   = NoData
--   map f (Data v) = Data $ f v
--
-- export
-- Foldable ReadRes where
--   foldl acc v (Err e)  = v
--   foldl acc v NoData   = v
--   foldl acc v (Data x) = acc v x
--
--   foldr acc v (Err e)  = v
--   foldr acc v NoData   = v
--   foldr acc v (Data x) = acc x v
--
--   foldMap f (Err e)  = neutral
--   foldMap f NoData   = neutral
--   foldMap f (Data x) = f x
--
--   toList (Err e)  = []
--   toList NoData   = []
--   toList (Data x) = [x]
--
-- export
-- Traversable ReadRes where
--   traverse f (Err e)  = pure $ Err e
--   traverse f NoData   = pure NoData
--   traverse f (Data x) = Data <$> f x
--
-- export
-- codeToRes : Int32 -> ReadRes Bits32
-- codeToRes 0 = NoData
-- codeToRes n = if n < 0 then Err (fromCode n) else Data (cast n)
--
-- readRes : HasIO io => Ptr Buf -> Ptr Fs -> io (ReadRes ByteString)
-- readRes buf fs = do
--   c <- uv_fs_get_result fs
--   traverse (toByteString buf) (codeToRes c)
--
-- readAndReleaseRes : HasIO io => Ptr Buf -> Ptr Fs -> io (ReadRes ByteString)
-- readAndReleaseRes buf fs = do
--   res <- readRes buf fs
--   freeBuf buf
--   releaseFs fs
--   pure res
--
-- ||| Asynchronously reads up to the given number of bytes from the given file.
-- export
-- fsReadBytes :
--      {auto l : UVLoop}
--   -> (file   : File)
--   -> (bytes  : Bits32)
--   -> (cb     : ReadRes ByteString -> IO ())
--   -> IO ()
-- fsReadBytes f bytes cb = do
--   fr  <- mallocPtr Fs
--   buf <- mallocBuf bytes
--   res <- uv_fs_read l.loop fr f.file buf 1 0 $ \fr =>
--     readAndReleaseRes buf fr >>= cb
--   case uvRes res of
--     Left err => freeBuf buf >> releaseFs fr >> cb (Err err)
--     _        => pure ()
--
-- ||| Tries to open the given file and to
-- ||| asynchronously read up to the given number of bytes.
-- export
-- readBytes :
--      {auto l : UVLoop}
--   -> (path   : String)
--   -> (bytes  : Bits32)
--   -> (cb     : ReadRes ByteString -> IO ())
--   -> UVIO ()
-- readBytes path bytes cb =
--   fsOpen path RDONLY neutral $
--     \case Left err => cb (Err err)
--           Right f  => fsReadBytes f bytes (\r => fsClose f >> cb r)
--
-- ||| Tries to open the given file and to
-- ||| asynchronously read up to the given number of bytes.
-- |||
-- ||| The data read is interpreted as a UTF8-encoded string.
-- export %inline
-- readText :
--      {auto l : UVLoop}
--   -> (path   : String)
--   -> (bytes  : Bits32)
--   -> (cb     : ReadRes String -> IO ())
--   -> UVIO ()
-- readText path bytes cb =
--   readBytes path bytes (cb . map toString)

--------------------------------------------------------------------------------
-- File Writing
--------------------------------------------------------------------------------

export
writeBytes :
     {auto l   : UVLoop}
  -> (openFile : (Either UVError (IO (), File) -> IO ()) -> IO ())
  -> (offset   : Int64)
  -> (onErr    : UVError -> IO ())
  -> Sink [] ByteString
writeBytes openFile offset onErr = MkSink $ \fuel => do
  fs <- mallocPtr Fs
  sr <- pipeRef [] ByteString (releaseFs fs)
  openFile $ \case
    Left err     => onErr err >> close sr
    Right (io,h) => appendResource sr io >> request sr (cb fuel sr fs h)
  pure (sink sr)

  where
    cb :
         Fuel
      -> PipeRef [] ByteString
      -> Ptr Fs
      -> File
      -> Callback [] ByteString
    cb Dry      sr fs h _ = close sr

    cb (More x) sr fs h (Next vs) = do
      buf <- fromByteString (fastConcat vs)
      res <- uv_fs_write l.loop fs h.file buf 1 offset
        (\p => freeBuf buf >> request sr (cb x sr fs h))
      case uvRes res of
        Left err => close sr >> freeBuf buf >> onErr err
        _        => pure ()

    cb _        sr fs h (Done vs) = do
      buf <- fromByteString (fastConcat vs)
      res <- uv_fs_write l.loop fs h.file buf 1 offset
        (\p => freeBuf buf >> close sr)
      case uvRes res of
        Left err => freeBuf buf >> close sr >> onErr err
        _        => pure ()

    cb sr fs h (Err err) impossible

export %inline
writeFile : UVLoop => (path : String) -> Flags -> Mode -> Sink [] ByteString
writeFile p fs m =
  writeBytes (fsOpen p (WRONLY <+> fs) m) (-1) (\_ => pure ())

export %inline
toFile : UVLoop => (path : String) -> Sink [] ByteString
toFile p = writeFile p CREAT 0o644

export %inline
appendToFile : UVLoop => (path : String) -> Sink [] ByteString
appendToFile p = writeFile p (CREAT <+> APPEND) 0o644

||| Sink that writes all bytes to `stdout`.
export %inline
bytesOut : UVLoop => Sink [] ByteString
bytesOut = writeBytes (\f => f $ Right (pure (), stdout)) 0 (\_ => pure ())

||| Sink that writes all text to `stdout`.
export %inline
putOut : UVLoop => Sink [] String
putOut = map fromString >- bytesOut

||| Sink that writes all text to `stdout`, interpreting
||| every item as a single line
export %inline
putOutLn : UVLoop => Sink [] String
putOutLn = map (fromString . (++ "\n")) >- bytesOut

||| Sink that printes values to `stdout` using their `Show`
||| implementation.
export %inline
printOut : UVLoop => Show a => Sink [] a
printOut = map (fromString . show) >- bytesOut

||| Sink that printes values to `stdout` using their `Show`
||| implementation and putting every item on a single line.
export %inline
printOutLn : UVLoop => Show a => Sink [] a
printOutLn = map (fromString . (++ "\n") . show) >- bytesOut

||| Sink that writes all bytes to `stderr`.
export %inline
bytesErr : UVLoop => Sink [] ByteString
bytesErr = writeBytes (\f => f $ Right (pure (), stderr)) 0 (\_ => pure ())

||| Sink that writes all text to `stderr`.
export %inline
putErr : UVLoop => Sink [] String
putErr = map fromString >- bytesErr

||| Sink that writes all text to `stderr`, interpreting
||| every item as a single line
export %inline
putErrLn : UVLoop => Sink [] String
putErrLn = map (fromString . (++ "\n")) >- bytesErr

||| Sink that printes values to `stderr` using their `Show`
||| implementation.
export %inline
printErr : UVLoop => Show a => Sink [] a
printErr = map (fromString . show) >- bytesErr

||| Sink that printes values to `stderr` using their `Show`
||| implementation and putting every item on a single line.
export %inline
printErrLn : UVLoop => Show a => Sink [] a
printErrLn = map (fromString . (++ "\n") . show) >- bytesErr

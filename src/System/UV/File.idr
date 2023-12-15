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
export
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

export
openFile :
     {auto l : UVLoop}
  -> String
  -> Flags
  -> Mode
  -> Source [UVError] (IO (), File)
openFile path fs m = MkSource $ do
  ref <- sourceRef [UVError] (IO (), File) (pure ())
  pure $ coldSrc ref $ \cb => fsOpen path fs m $ \case
    Left err => cb (Err $ inject err)
    Right p  => cb (Done [p])

--------------------------------------------------------------------------------
-- File Reading
--------------------------------------------------------------------------------

codeToMsg : Int32 -> Msg [UVError] Bits32
codeToMsg 0 = Done []
codeToMsg n = if n < 0 then Err (inject $ fromCode n) else Next [cast n]

readRes : Ptr Buf -> Ptr Fs -> IO (Msg [UVError] ByteString)
readRes buf fs = do
  c <- uv_fs_get_result fs
  traverse (toByteString buf) (codeToMsg c)

export
readBytes :
     {auto l : UVLoop}
  -> (file   : File)
  -> (close  : IO ())
  -> (buffer : Bits32)
  -> Source [UVError] ByteString
readBytes f close buffer = MkSource $ do
  fs  <- mallocPtr Fs
  buf <- mallocBuf buffer
  ref <- sourceRef [UVError] ByteString (releaseFs fs >> freeBuf buf >> close)
  pure (coldSrc ref $ read fs buf)
    where
      read : Ptr Fs -> Ptr Buf -> Callback [UVError] ByteString -> IO ()
      read fs buf cb = do
        setBufLen buf buffer
        res <- uv_fs_read l.loop fs f.file buf 1 (-1)
          (\p => readRes buf p >>= cb)
        case uvRes res of
          Left err => cb (Err $ inject err)
          Right () => pure ()

export
readStdIn : UVLoop => Source [UVError] ByteString
readStdIn = readBytes stdin (pure ()) 4096

export covering
readFile : UVLoop => (path : String) -> Source [UVError] ByteString
readFile path =
  openFile path RDONLY 0 |> flatMap (\(cl,f) => readBytes f cl 0xffff)

--------------------------------------------------------------------------------
-- File Writing
--------------------------------------------------------------------------------

export
printErrs : (l : UVLoop) => (ps : All Interpolation es) => Pipe es [] a a
printErrs =
  handle $ \es => do
    fs <- mallocPtr Fs
    let s := collapse' $ hzipWith (\_,e => interpolate e) ps es
    buf <- fromByteString (fromString s)
    ignore $ uv_fs_write l.loop fs stderr.file buf 1 (-1)
      (\p => freeBuf buf >> releaseFs p)

export
writeBytes :
     {auto l   : UVLoop}
  -> (openFile : (Either UVError (IO (), File) -> IO ()) -> IO ())
  -> (offset   : Int64)
  -> (onErr    : UVError -> IO ())
  -> Sink [] ByteString
writeBytes openFile offset onErr = MkSink $ \fuel => do
  fs <- mallocPtr Fs
  sr <- sinkRef [] ByteString (releaseFs fs)
  openFile $ \case
    Left err     => onErr err >> close sr
    Right (io,h) => appendResource sr io >> request sr (cb fuel sr fs h)
  pure (sink sr)

  where
    cb :
         Fuel
      -> SinkRef [] ByteString
      -> Ptr Fs
      -> File
      -> Callback [] ByteString
    cb Dry      sr fs h _ = close sr

    cb (More x) sr fs h (Next []) = request sr (cb x sr fs h)
    cb (More x) sr fs h (Next vs) = do
      buf <- fromByteString (fastConcat vs)
      res <- uv_fs_write l.loop fs h.file buf 1 offset
        (\p => freeBuf buf >> request sr (cb x sr fs h))
      case uvRes res of
        Left err => close sr >> freeBuf buf >> onErr err
        _        => pure ()

    cb _        sr fs h (Done []) = abort sr
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
bytesOut = writeBytes (\f => f $ Right (pure (), stdout)) (-1) (\_ => pure ())

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

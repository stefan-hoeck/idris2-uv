module System.UV.File

import Data.Buffer
import Data.Maybe
import System.UV.Loop
import System.UV.Pointer
import System.UV.Util

import public Data.Buffer.Indexed
import public Data.ByteString

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

export %inline
fsClose : HasIO io => (l : UVLoop) => File -> io ()
fsClose f = ignore $ uv_fs_close_sync l.loop f.file

export %inline
UVLoop => Resource File where
  release = fsClose

export
Resource (Ptr Fs) where
  release p = uv_fs_req_cleanup p >> freePtr p

parameters {auto l   : UVLoop}
           {auto has : Has UVError es}

  fileOutcome : (Outcome es File -> IO ()) -> Ptr Fs -> IO ()
  fileOutcome cb p = do
    n <- uv_fs_get_result p
    if n < 0
      then cb (Error . inject $ fromCode n)
      else cb (Succeeded $ MkFile n)

  ||| Asynchronously opens a file.
  export
  fsOpen : String -> Flags -> Mode -> Async es File
  fsOpen path f m = do
    use1 (mallocPtr Fs) $ \fs =>
      uvAsync $ uv_fs_open l.loop fs path f.flags m.mode . fileOutcome

--------------------------------------------------------------------------------
-- File Writing
--------------------------------------------------------------------------------

parameters {auto l   : UVLoop}
           {auto has : Has UVError es}

  export
  writeBytesAt : File -> (offset : Int64) -> ByteString -> Async es ()
  writeBytesAt h offset bs =
    useMany [mallocPtr Fs, fromByteString bs] $ \[fs,buf] =>
      uvAsync $ \cb =>
        uv_fs_write l.loop fs h.file buf 1 offset $ \_ => cb (Succeeded ())

  export %inline
  writeBytes : File -> ByteString -> Async es ()
  writeBytes h = writeBytesAt h (-1)

  export %inline
  writeFile : (path : String) -> Flags -> Mode -> ByteString -> Async es ()
  writeFile p fs m bs =
    use1 (fsOpen p (WRONLY <+> fs) m) $ \h => writeBytes h bs

  export %inline
  toFile : (path : String) -> ByteString -> Async es ()
  toFile p = writeFile p CREAT 0o644

  export %inline
  appendToFile : (path : String) -> ByteString -> Async es ()
  appendToFile p = writeFile p (CREAT <+> APPEND) 0o644

  ||| Writes all bytes to `stdout`.
  export %inline
  bytesOut : ByteString -> Async es ()
  bytesOut = writeBytes stdout

  ||| Write some text to `stdout`.
  export %inline
  putOut : String -> Async es ()
  putOut = bytesOut . fromString

  ||| Sink that writes all text to `stdout`, interpreting
  ||| every item as a single line
  export %inline
  putOutLn : String -> Async es ()
  putOutLn = putOut . (++ "\n")

  ||| Sink that printes values to `stdout` using their `Show`
  ||| implementation.
  export %inline
  printOut : Show a => a -> Async es ()
  printOut = putOut . show

  ||| Sink that printes values to `stdout` using their `Show`
  ||| implementation and putting every item on a single line.
  export %inline
  printOutLn : Show a => a -> Async es ()
  printOutLn = putOutLn . show

  ||| Writes all bytes to `stderr`.
  export %inline
  bytesErr : ByteString -> Async es ()
  bytesErr = writeBytes stderr

  ||| Write some text to `stderr`.
  export %inline
  putErr : String -> Async es ()
  putErr = bytesErr . fromString

  ||| Sink that writes all text to `stderr`, interpreting
  ||| every item as a single line
  export %inline
  putErrLn : String -> Async es ()
  putErrLn = putErr . (++ "\n")

  ||| Sink that printes values to `stderr` using their `Show`
  ||| implementation.
  export %inline
  printErr : Show a => a -> Async es ()
  printErr = putErr . show

  ||| Sink that printes values to `stderr` using their `Show`
  ||| implementation and putting every item on a single line.
  export %inline
  printErrLn : Show a => a -> Async es ()
  printErrLn = putErrLn . show

--------------------------------------------------------------------------------
-- File Reading
--------------------------------------------------------------------------------

export
record ReadBuffer where
  constructor RB
  ptr  : Ptr Buf
  size : Bits32

export %inline
mkBuffer : HasIO io => Bits32 -> io (ReadBuffer)
mkBuffer n = do
  buf <- mallocBuf n
  pure (RB buf n)

export
Resource ReadBuffer where
  release b = freeBuf b.ptr

codeToMsg : Has UVError es => Int32 -> Outcome es (Maybe Bits32)
codeToMsg 0 = Succeeded Nothing
codeToMsg n = toOutcome (uvRes n $> (Just $ cast n))

parameters {auto l   : UVLoop}
           {auto has : Has UVError es}

  readRes :
       Ptr Buf
    -> Ptr Fs
    -> IO (Outcome es (Maybe ByteString))
  readRes buf fs = do
    c <- uv_fs_get_result fs
    traverse (traverse (toByteString buf)) (codeToMsg c)

  export
  readBytesInto : File -> (buf : ReadBuffer) -> Async es (Maybe ByteString)
  readBytesInto f (RB buf n) =
    use1 (mallocPtr Fs) $ \fs => do
      setBufLen buf n
      uvAsync $ \cb =>
        uv_fs_read l.loop fs f.file buf 1 (-1) $ \p => readRes buf p >>= cb

  export
  readBytes : File -> Bits32 -> Async es ByteString
  readBytes f n =
    use1 (mkBuffer n) $ \buf =>
      fromMaybe empty <$> readBytesInto f buf

  export
  readStdIn : Async es ByteString
  readStdIn = readBytes stdin 4096

  export covering
  readFile : (path : String) -> Bits32 -> Async es ByteString
  readFile path n =
    use1 (fsOpen path RDONLY 0) $ \f => readBytes f n

  export covering
  streamFileInto :
       (path : String)
    -> (buf  : ReadBuffer)
    -> (ByteString -> Async es (Maybe b))
    -> Async es (Maybe b)
  streamFileInto {b} path buf fun =
    use1 (fsOpen path RDONLY 0) $ \h => cancelable $ go h
    where
      go : File -> Async es (Maybe b)
      go h = do
        Just v  <- readBytesInto h buf | Nothing  => pure Nothing
        Nothing <- fun v               | Just res => pure (Just res)
        go h

  export covering
  streamFileUntil :
       (path : String)
    -> Bits32
    -> (ByteString -> Async es (Maybe b))
    -> Async es (Maybe b)
  streamFileUntil {b} path n fun =
    use1 (mkBuffer n) $ \b => streamFileInto path b fun

  export covering
  streamFile :
       (path : String)
    -> Bits32
    -> (ByteString -> Async es ())
    -> Async es (Maybe ())
  streamFile path n fun =
    streamFileUntil path n (\x => fun x $> Nothing)

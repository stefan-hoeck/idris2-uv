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
fsClose f = ignore . sync $ uv_fs_close l.loop f.file

export %inline
UVLoop => Resource File where
  release = fsClose

parameters {auto l   : UVLoop}
           {auto has : Has UVError es}

  fsOutcome : (Outcome es Int32 -> IO ()) -> Ptr Fs -> IO ()
  fsOutcome cb p = do
    n <- uv_fs_get_result p
    if n < 0
      then cb (Error . inject $ fromCode n)
      else cb (Succeeded n)

  fileOutcome : (Outcome es File -> IO ()) -> Ptr Fs -> IO ()
  fileOutcome cb = fsOutcome (cb . map MkFile)

  ||| Asynchronously opens a file.
  export
  fsOpen : String -> Flags -> Mode -> Async es File
  fsOpen path f m =
    uvAsync $ async (uv_fs_open l.loop path f.flags m.mode) . fileOutcome

  export %inline
  readOpen : String -> Async es File
  readOpen s = fsOpen s RDONLY 0

  export %inline
  writeOpen : String -> Async es File
  writeOpen s = fsOpen s (WRONLY <+> CREAT) 0o644

  export %inline
  appendOpen : String -> Async es File
  appendOpen s = fsOpen s (WRONLY <+> CREAT <+> APPEND) 0o644

--------------------------------------------------------------------------------
-- File Writing
--------------------------------------------------------------------------------

parameters {auto l   : UVLoop}
           {auto has : Has UVError es}

  writeOutcome : (Outcome es () -> IO ()) -> Ptr Fs -> IO ()
  writeOutcome cb = fsOutcome (cb . ignore)

  export
  writeBytesAt : File -> (offset : Int64) -> ByteString -> Async es ()
  writeBytesAt h offset bs =
    use1 (fromByteString bs) $ \cs =>
      uvAsync $ \cb => do
        async
          (uv_fs_write l.loop h.file cs (cast bs.size) offset)
          (writeOutcome cb)

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

parameters {auto l   : UVLoop}
           {auto has : Has UVError es}

  readOutcome : Ptr Bits8 -> (Outcome es ByteString -> IO ()) -> Ptr Fs -> IO ()
  readOutcome cs cb =
    fsOutcome {es} $ \case
      Succeeded res => toByteString cs (cast res) >>= cb . Succeeded
      Error err => cb (Error err)
      Canceled  => cb Canceled

  export
  readBytes : File -> Bits32 -> Async es ByteString
  readBytes f size =
    use1 (mallocPtrs Bits8 size) $ \cs =>
      uvAsync $ \cb => do
        async (uv_fs_read l.loop f.file cs size (-1)) (readOutcome cs cb)

  export
  readStdIn : Async es ByteString
  readStdIn = readBytes stdin 4096

  export
  readFile : (path : String) -> Bits32 -> Async es ByteString
  readFile path n = use1 (readOpen path) (`readBytes` n)

  export covering
  streamFileUntil :
       (path : String)
    -> Bits32
    -> (ByteString -> Async es (Maybe b))
    -> Async es (Maybe b)
  streamFileUntil {b} path size fun = use1 (readOpen path) go
    where
      go : File -> Async es (Maybe b)
      go h = do
        v  <- readBytes h size
        if null v
           then pure Nothing
           else fun v >>= maybe (go h) (pure . Just)

  export covering
  streamFile :
       (path : String)
    -> Bits32
    -> (ByteString -> Async es ())
    -> Async es ()
  streamFile path n fun =
    ignore $ streamFileUntil {b = ()} path n (\x => fun x $> Nothing)

  export covering
  streamLinesUntil :
       (path : String)
    -> Bits32
    -> (List ByteString -> Async es (Maybe b))
    -> Async es (Maybe b)
  streamLinesUntil {b} path size fun = use1 (readOpen path) (go empty)
    where
      go : ByteString -> File -> Async es (Maybe b)
      go rem h = do
        v  <- readBytes h size
        if null v
           then fun $ if null rem then [] else [rem]
           else
             let (ls,rem2) := accumLines rem v
              in fun ls >>= maybe (go rem2 h) (pure . Just)

  export covering
  streamLines :
       (path : String)
    -> Bits32
    -> (List ByteString -> Async es ())
    -> Async es ()
  streamLines path size fun =
    ignore $ streamLinesUntil {b = ()} path size (\xs => fun xs $> Nothing)

  export covering
  foldBytes :
       (path : String)
    -> Bits32
    -> (s -> ByteString -> s)
    -> s
    -> Async es s
  foldBytes {s} path size acc ini =
    use1 (readOpen path) (go ini)

    where
      go : s -> File -> Async es s
      go cur h = do
        v  <- readBytes h size
        if null v then pure cur else go (acc cur v) h

  export covering
  foldLines :
       (path : String)
    -> Bits32
    -> (s -> ByteString -> s)
    -> s
    -> Async es s
  foldLines {s} path size acc ini =
    term <$> foldBytes path size accB (empty,ini)

    where
      term : (ByteString, s) -> s
      term (bs,s) = if null bs then s else acc s bs

      accB : (ByteString, s) -> ByteString -> (ByteString,s)
      accB (rem,cur) v =
        let (ls,rem2) := accumLines rem v
         in (rem2, foldl acc cur ls)

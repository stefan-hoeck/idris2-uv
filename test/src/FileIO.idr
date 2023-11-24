module FileIO

import System.UV
import System.UV.File
import System.UV.File.Flags

parameters {auto l : Loop}
           (openReq, readReq, writeReq : Ptr Fs)
           (iov : Ptr Buf)

  onWrite : File -> Maybe UVError -> UVIO ()

  onRead : File -> ReadRes Bits32 -> UVIO ()

  onWrite h (Just err) = putStrLn "Write error: \{err}"
  onWrite h Nothing    = fsRead readReq h iov 1 (-1) (runUVIO . onRead h)

  onRead h (Err err) = putStrLn "Read error: \{err}"
  onRead h NoData    = fsClose h
  onRead h (Data n)  = do
    setBufLen iov (cast n)
    fsWrite writeReq stdout iov 1 (-1) (runUVIO . onWrite h)

  onOpen : Either UVError File -> UVIO ()
  onOpen (Left err) = putStrLn "Opening error: \{err}"
  onOpen (Right h)  = fsRead readReq h iov 1 (-1) (runUVIO . onRead h)

export
main : IO ()
main = do
  fo  <- mallocPtr Fs
  fr  <- mallocPtr Fs
  fw  <- mallocPtr Fs
  iov <- mallocBuf 0xffff

  runUV $ fsOpen fo "pack.toml" RDONLY neutral (runUVIO . onOpen fo fr fw iov)
  fsCleanup fo
  fsCleanup fr
  fsCleanup fw
  freePtr fo
  freePtr fr
  freePtr fw
  freeBuf iov

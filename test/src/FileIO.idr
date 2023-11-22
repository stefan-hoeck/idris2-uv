module FileIO

import System.UV
import System.UV.File
import System.UV.File.Flags

parameters {auto l : Loop}
           (openReq, readReq, writeReq : Ptr Fs)
           (iov : Ptr Buf)

  onWrite : Ptr Fs -> UVIO ()

  onRead : Ptr Fs -> UVIO ()

  onOpen : Ptr Fs -> UVIO ()

  onWrite req = do
    n  <- fsResult req
    oh <- fsResult openReq
    if n < 0
       then putStrLn "Write error: \{fromCode n}"
       else fsRead readReq oh iov 1 (-1) (runUVIO . onRead)

  onRead req = do
    n  <- fsResult req
    oh <- fsResult openReq
    if n < 0
       then putStrLn "Read error: \{fromCode n}"
       else
         if n == 0
            then do
              closeReq <- mallocReq FS
              fsClose closeReq oh (const unitIO)
            else do
              setBufLen iov (cast n)
              fsWrite writeReq 1 iov 1 (-1) (runUVIO . onWrite)

  onOpen req = do
    n  <- fsResult req
    oh <- fsResult openReq
    if n < 0
       then putStrLn "Opening error: \{fromCode n}"
       else fsRead readReq oh iov 1 (-1) (runUVIO . onRead)

export
main : IO ()
main = do
  fo  <- mallocReq FS
  fr  <- mallocReq FS
  fw  <- mallocReq FS
  iov <- allocBuf 0xffff

  runUV $ fsOpen fo "pack.toml" RDONLY neutral (runUVIO . onOpen fo fr fw iov)
  fsCleanup fo
  fsCleanup fr
  fsCleanup fw
  freeHandle fo
  freeHandle fr
  freeHandle fw
  freeBuf iov

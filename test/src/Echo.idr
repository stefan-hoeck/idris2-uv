module Echo

import System.UV
import System.UV.DNS
import System.UV.File
import System.UV.Stream
import System.UV.TCP

%default total

allocBuf : Bits32 -> Ptr Buf -> IO ()
allocBuf s buf = do
  cs <- mallocPtrs String s
  setBufBase buf cs
  setBufLen buf s

echoWrite : Ptr Buf -> Ptr Write -> Int32 -> IO ()
echoWrite buf p res = do
  when (res < 0) $ putStrLn "Write error \{fromCode res}"
  freePtr p

echoRead : Ptr Stream -> Int32 -> Ptr Buf -> IO ()
echoRead client nread buf = do
  case codeToRes nread of
    Err err => do
      if err.code == UV_EOF 
         then putStrLn "Connection closed by peer."
         else putStrLn "Read error: \{err}"
      close client freePtr
      freeBufBase buf
    NoData  => freeBufBase buf
    Data x  => do
      putStrLn "Got some data!"
      req  <- mallocPtr Write
      runUVIO $ write req client buf 1 (echoWrite buf)

onNewConnection : Loop => Ptr Stream -> Int32 -> IO ()
onNewConnection server status =
  if status < 0
     then putStrLn "New connection error: \{fromCode status}"
     else do
       client <- mallocPtr Tcp
       runUVIO $ tcpInit client
       Right () <- runEitherT $ accept server client
         | Left err => close client freePtr
       putStrLn "Connection accepted"
       runUVIO $ readStart client (\_ => allocBuf) echoRead

onResolved : Loop => Ptr GetAddrInfo -> Int32 -> Ptr AddrInfo -> IO ()
onResolved _ status res = runUVIO $ do
  checkStatus status
  addr <- getAddr res
  str  <- ip4Name addr
  putStrLn "Address resolved: \{str}"
  server <- mallocPtr Tcp
  tcpInit server
  tcpBind server addr 0
  listen server 128 onNewConnection
  freeAddrInfo res

prog : Loop => UVIO ()
prog = do
  hints  <- mallocPtr AddrInfo
  res    <- mallocPtr GetAddrInfo
  setFamily hints AF_INET
  setSockType hints Stream
  getAddrInfo res onResolved "localhost" "6000" hints

export
main : IO ()
main = runUV prog

module Echo

import System.UV
import System.UV.File
import System.UV.Stream
import System.UV.TCP

%default total

allocBuf : Bits32 -> Ptr Buf -> IO ()
allocBuf s buf = do
  cs <- mallocPtrs Char s
  setBufBase buf cs
  setBufLen buf s

echoWrite : Ptr Buf -> Ptr Write -> Int32 -> IO ()
echoWrite buf p res = do
  when (res < 0) $ putStrLn "Write error \{fromCode res}"
  freeBufBase buf
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
      buf2 <- mallocPtr Buf 
      base <- getBufBase buf
      initBuf buf2 base x
      runUVIO $ write req client buf2 1 (echoWrite buf)

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

printSize : HasIO io => {s : _} -> (0 p : PSize a s) -> String -> io ()
printSize _ name = putStrLn "sizeof(\{name}) = \{show s}"

prog : Loop => UVIO ()
prog = do
  server <- mallocPtr Tcp
  addr   <- mallocPtr SockAddrIn

  tcpInit server
  ip4Addr "127.0.0.1" 6000 addr
  tcpBind server addr 0
  putStrLn "Listening on 127.0.0.1 on port 6000"
  listen server 128 onNewConnection

export
main : IO ()
main = runUV prog
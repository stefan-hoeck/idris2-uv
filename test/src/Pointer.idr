module Pointer

import System.UV.Raw.Pointer

%default total

check : {s : _} -> PSize t s -> String
check p = "size allocated for \{show p} is \{show s} bytes"

-- this just checks that every pointer size is correctly named
-- in the FFI
export
run : IO ()
run = do
  traverse_ putStrLn
    [ check ASYNC
    , check CHECK
    , check FS_EVENT
    , check FS_POLL
    , check HANDLE
    , check IDLE
    , check NAMEDPIPE
    , check POLL
    , check PREPARE
    , check PROCESS
    , check STREAM
    , check TCP
    , check TIMER
    , check TTY
    , check UDP
    , check SIGNAL
    , check REQ
    , check CONNECT
    , check WRITE
    , check SHUTDOWN
    , check FS
    , check WORK
    , check GETADDRINFO
    , check GETNAMEINFO
    , check ADDRINFO
    , check SOCKADDR
    , check SOCKADDRIN
    , check SOCKADDRIN6
    , check BUF
    , check BYTE
    , check CHAR
    ]

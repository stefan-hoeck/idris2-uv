module System.UV.TCP

import IO.Async.Event
import System.UV.Loop
import System.UV.Pointer
import System.UV.Stream
import System.UV.Raw.Handle
import System.UV.Raw.Stream
import System.UV.Raw.TCP

%default total

export
Resource (Ptr SockAddrIn) where
  release = freePtr

export %inline
(cc : CloseCB) => Resource (Ptr Tcp) where
  release h = uv_close h cc

||| Convert a binary structure containing an IPv4 address to a string.
export
ip4name : Ptr SockAddrIn -> IO String
ip4name p = do
  cs <- mallocPtrs Char 256
  r  <- uv_ip4_name p cs 255
  let res = getString cs
  freePtr cs
  pure res

||| Convert a binary structure containing an IPv6 address to a string.
export
ip6name : Ptr SockAddrIn6 -> IO String
ip6name p = do
  cs <- mallocPtrs Char 256
  r  <- uv_ip6_name p cs 255
  let res = getString cs
  freePtr cs
  pure res

||| Convert a binary structure containing an IPv4 address or an
||| IPv6 address to a string.
export
ipname : Ptr SockAddr -> IO String
ipname p = do
  cs <- mallocPtrs Char 256
  r  <- uv_ip_name p cs 255
  let res = getString cs
  freePtr cs
  pure res

parameters {auto l : UVLoop}
           {auto has : Has UVError es}

  export
  mkTcp : Async es (Ptr Tcp)
  mkTcp = mallocPtr Tcp >>= uvAct (uv_tcp_init l.loop)

  export
  bindTcp : Ptr SockAddrIn -> Async es (Ptr Tcp)
  bindTcp addr = mkTcp >>= uvAct (\x => uv_tcp_bind x addr 0)

  export
  acceptTcp : Ptr Stream -> Async es (Ptr Tcp)
  acceptTcp server = mkTcp >>= uvAct (\x => uv_accept server x)

  export covering
  listenTcp :
       (addresss : String)
    -> (port     : Bits16)
    -> (run      : Buffer (Either UVError (Ptr Stream)) -> Async es ())
    -> Async es ()
  listenTcp address port run =
    use1 (mallocPtr SockAddrIn) $ \addr => do
      uv (uv_ip4_addr address port addr)
      use1 (bindTcp addr) $ \server => listen server run

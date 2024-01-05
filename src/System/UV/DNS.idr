module System.UV.DNS

import Derive.Prelude
import System.FFI
import System.UV.Pointer
import System.UV.Loop
import System.UV.Util
import public System.UV.Raw.DNS

%language ElabReflection
%default total

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

public export
record SockInfo where
  constructor SI
  family   : SockFamily
  type     : SockType
  protocol : Protocol

hints : HasIO io => SockInfo -> io (Ptr AddrInfo)
hints (SI f t p) = do
  hs <- mallocPtr AddrInfo
  uv_set_ai_family   hs (familyCode f)
  uv_set_ai_socktype hs (sockCode t)
  uv_set_ai_protocol hs (protocolCode p)
  pure hs

export
Resource (Ptr AddrInfo) where
  release = uv_freeaddrinfo

export
Resource (Ptr GetAddrInfo) where
  release = freePtr

parameters {auto l   : UVLoop}
           {auto has : Has UVError es}

  gaCB :
       (Outcome es (Ptr AddrInfo) -> IO ())
    -> Ptr GetAddrInfo
    -> Int32
    -> Ptr AddrInfo
    -> IO ()
  gaCB cb _ st pa = do
    case uvRes st of
      Left err => uv_freeaddrinfo pa >> cb (Error err)
      Right () => cb (Succeeded pa)

  export
  addrInfo : (node, service : String) -> SockInfo -> Async es (Ptr AddrInfo)
  addrInfo n s h =
    use [hints h, mallocPtr GetAddrInfo] $ \[hs,pg] => do
      uvAsync $ \cb => uv_getaddrinfo l.loop pg (gaCB cb) n s hs

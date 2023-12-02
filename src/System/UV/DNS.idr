module System.UV.DNS

import Derive.Prelude
import System.FFI
import System.UV.Error
import System.UV.Handle
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

export %inline
getAddrInfo :
     {auto l : UVLoop}
  -> (node, service : String)
  -> SockInfo
  -> (Either UVError (Ptr AddrInfo) -> IO ())
  -> UVIO ()
getAddrInfo n s (SI f t p) cb = do
  hints <- mallocPtr AddrInfo
  pg    <- mallocPtr GetAddrInfo
  uv_set_ai_family   hints (familyCode f)
  uv_set_ai_socktype hints (sockCode t)
  uv_set_ai_protocol hints (protocolCode p)
  res   <- uv_getaddrinfo
    l.loop
    pg
    (\pa,st,pa => freePtr pa >> freePtr hints >> cb (uvRes st $> pa))
    n
    s
    hints

  case uvRes res of
    Left err => freePtr hints >> freePtr pg >> left err
    Right _  => pure ()

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

||| Socket Families
|||
||| The ones that people might actually use. We're not going to need US
||| Government proprietary ones.
public export
data SockFamily : Type where
  ||| Unspecified
  AF_UNSPEC : SockFamily

  ||| Unix type sockets
  AF_UNIX : SockFamily

  ||| IP / UDP etc. IPv4
  AF_INET : SockFamily

  |||  IP / UDP etc. IPv6
  AF_INET6 : SockFamily

%runElab derive "SockFamily" [Show,Eq]

export
familyCode : SockFamily -> Int32
familyCode AF_UNSPEC = uv_af_unspec
familyCode AF_UNIX   = uv_af_unix
familyCode AF_INET   = uv_af_inet
familyCode AF_INET6  = uv_af_inet6

||| Socket Types.
public export
data SockType : Type where
  ||| Any socket type
  Any : SockType

  ||| TCP
  Stream : SockType

  ||| UDP
  Datagram : SockType

  ||| Raw sockets
  Raw : SockType

%runElab derive "SockType" [Show,Eq]

export
socketCode : SockType -> Int32
socketCode Any      = uv_sock_any
socketCode Stream   = uv_sock_stream
socketCode Datagram = uv_sock_dgram
socketCode Raw      = uv_sock_raw

public export
data Protocol : Type where
  IPPROTO_IP   : Protocol
  IPPROTO_IPV6 : Protocol
  IPPROTO_ICMP : Protocol
  IPPROTO_RAW  : Protocol
  IPPROTO_TCP  : Protocol
  IPPROTO_UDP  : Protocol

%runElab derive "Protocol" [Show,Eq]

export
protocolCode : Protocol -> Int32
protocolCode IPPROTO_IP   = uv_ipproto_ip
protocolCode IPPROTO_IPV6 = uv_ipproto_ipv6
protocolCode IPPROTO_ICMP = uv_ipproto_icmp
protocolCode IPPROTO_RAW  = uv_ipproto_raw
protocolCode IPPROTO_TCP  = uv_ipproto_tcp
protocolCode IPPROTO_UDP  = uv_ipproto_udp

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
  uv_set_ai_socktype hints (socketCode t)
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

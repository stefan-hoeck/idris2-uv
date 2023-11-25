module System.UV.DNS

import Derive.Prelude
import System.FFI
import System.UV.Error
import System.UV.Handle
import System.UV.Pointer
import System.UV.Loop
import System.UV.Util

%language ElabReflection
%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_set_ai_family")
uv_set_ai_family : Ptr AddrInfo -> Int32 -> PrimIO ()

%foreign (idris_uv "uv_set_ai_socktype")
uv_set_ai_socktype : Ptr AddrInfo -> Int32 -> PrimIO ()

%foreign (idris_uv "uv_set_ai_protocol")
uv_set_ai_protocol : Ptr AddrInfo -> Int32 -> PrimIO ()

%foreign (idris_uv "uv_set_ai_flags")
uv_set_ai_flags : Ptr AddrInfo -> Int32 -> PrimIO ()

%foreign (idris_uv "uv_get_ai_family")
uv_get_ai_family : Ptr AddrInfo -> PrimIO Int32

%foreign (idris_uv "uv_get_ai_socktype")
uv_get_ai_socktype : Ptr AddrInfo -> PrimIO Int32

%foreign (idris_uv "uv_get_ai_protocol")
uv_get_ai_protocol : Ptr AddrInfo -> PrimIO Int32

%foreign (idris_uv "uv_get_ai_flags")
uv_get_ai_flags : Ptr AddrInfo -> PrimIO Int32

%foreign (idris_uv "uv_get_ai_addr")
uv_get_ai_addr : Ptr AddrInfo -> PrimIO (Ptr SockAddr)

%foreign (idris_uv "uv_freeaddrinfo")
uv_freeaddrinfo : Ptr AddrInfo -> PrimIO ()

export %foreign (idris_uv "uv_af_inet")
uv_af_inet : Int32

export %foreign (idris_uv "uv_af_inet6")
uv_af_inet6 : Int32

export %foreign (idris_uv "uv_af_unix")
uv_af_unix : Int32

export %foreign (idris_uv "uv_af_unspec")
uv_af_unspec : Int32

export %foreign (idris_uv "uv_sock_stream")
uv_sock_stream : Int32

export %foreign (idris_uv "uv_sock_dgram")
uv_sock_dgram : Int32

export %foreign (idris_uv "uv_sock_raw")
uv_sock_raw : Int32

export %foreign (idris_uv "uv_sock_any")
uv_sock_any : Int32

export %foreign (idris_uv "uv_ipproto_ip")
uv_ipproto_ip : Int32

export %foreign (idris_uv "uv_ipproto_ipv6")
uv_ipproto_ipv6 : Int32

export %foreign (idris_uv "uv_ipproto_icmp")
uv_ipproto_icmp : Int32

export %foreign (idris_uv "uv_ipproto_raw")
uv_ipproto_raw : Int32

export %foreign (idris_uv "uv_ipproto_tcp")
uv_ipproto_tcp : Int32

export %foreign (idris_uv "uv_ipproto_udp")
uv_ipproto_udp : Int32

%foreign (idris_uv "uv_getaddrinfo")
uv_getaddrinfo :
     Ptr LoopPtr
  -> Ptr GetAddrInfo
  -> (Ptr GetAddrInfo -> Int32 -> Ptr AddrInfo -> PrimIO ())
  -> (node, service : String)
  -> (hints : Ptr AddrInfo)
  -> PrimIO Int32

%foreign (idris_uv "uv_getnameinfo")
uv_getnameinfo :
     Ptr LoopPtr
  -> Ptr GetNameInfo
  -> (Ptr GetAddrInfo -> Int32 -> (hostname, servie : Ptr Char) -> PrimIO ())
  -> Ptr SockAddr
  -> (flags : Int32)
  -> PrimIO Int32

%foreign (idris_uv "uv_ip4_name")
uv_ip4_name : Ptr SockAddrIn -> Ptr Char -> Bits32 -> PrimIO ()

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Socket Families
|||
||| The ones that people might actually use. We're not going to need US
||| Government proprietary ones.
public export
data SocketFamily : Type where
  ||| Unspecified
  AF_UNSPEC : SocketFamily

  ||| Unix type sockets
  AF_UNIX : SocketFamily

  ||| IP / UDP etc. IPv4
  AF_INET : SocketFamily

  |||  IP / UDP etc. IPv6
  AF_INET6 : SocketFamily

%runElab derive "SocketFamily" [Show,Eq]

export
familyCode : SocketFamily -> Int32
familyCode AF_UNSPEC = uv_af_unspec
familyCode AF_UNIX   = uv_af_unix
familyCode AF_INET   = uv_af_inet
familyCode AF_INET6  = uv_af_inet6

||| Socket Types.
public export
data SocketType : Type where
  ||| Any socket type
  Any : SocketType

  ||| TCP
  Stream : SocketType

  ||| UDP
  Datagram : SocketType

  ||| Raw sockets
  Raw : SocketType

%runElab derive "SocketType" [Show,Eq]

export
socketCode : SocketType -> Int32
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

export %inline
setFamily : HasIO io => Ptr AddrInfo -> SocketFamily -> io ()
setFamily p f = primIO $ uv_set_ai_family p (familyCode f)

export %inline
setSockType : HasIO io => Ptr AddrInfo -> SocketType -> io ()
setSockType p s = primIO $ uv_set_ai_socktype p (socketCode s)

export %inline
setProtocol : HasIO io => Ptr AddrInfo -> Protocol -> io ()
setProtocol p v = primIO $ uv_set_ai_protocol p (protocolCode v)

export %inline
setFlags : HasIO io => Ptr AddrInfo -> Int32 -> io ()
setFlags p v = primIO $ uv_set_ai_flags p v

export %inline
getFamily : HasIO io => Ptr AddrInfo -> io Int32
getFamily p = primIO $ uv_get_ai_family p

export %inline
getSockType : HasIO io => Ptr AddrInfo -> io Int32
getSockType p = primIO $ uv_get_ai_socktype p

export %inline
getProtocol : HasIO io => Ptr AddrInfo -> io Int32
getProtocol p = primIO $ uv_get_ai_protocol p

export %inline
getFlags : HasIO io => Ptr AddrInfo -> io Int32
getFlags p = primIO $ uv_get_ai_flags p

export %inline
getAddr : HasIO io => Ptr AddrInfo -> io (Ptr SockAddr)
getAddr p = primIO $ uv_get_ai_addr p

export %inline
freeAddrInfo : HasIO io => Ptr AddrInfo -> io ()
freeAddrInfo p = primIO $ uv_freeaddrinfo p

export %inline
getAddrInfo :
     {auto l : Loop}
  -> Ptr GetAddrInfo
  -> (Ptr GetAddrInfo -> Int32 -> Ptr AddrInfo -> IO ())
  -> (node, service : String)
  -> (hints : Ptr AddrInfo)
  -> UVIO ()
getAddrInfo pa cb n s h =
  primUV $ uv_getaddrinfo l.loop pa (\x,y,z => toPrim (cb x y z)) n s h

export %inline
getNameInfo :
     {auto l : Loop}
  -> Ptr GetNameInfo
  -> (Ptr GetAddrInfo -> Int32 -> (hostname, servie : Maybe String) -> IO ())
  -> Ptr SockAddr
  -> (flags : Int32)
  -> UVIO ()
getNameInfo pa cb sa flags =
  primUV $ uv_getnameinfo
    l.loop
    pa
    (\w,x,y,z => toPrim $ cb w x (getStringMay y) (getStringMay z))
    sa
    flags

export
ip4Name : HasIO io => (0 p : PCast t SockAddrIn) => Ptr t -> io String
ip4Name p = do
  str <- mallocPtrs Char 512
  primIO $ uv_ip4_name (castPtr p) str 511
  res <- pure $ getString str
  freePtr str
  pure res

module System.UV.Data.DNS

import Derive.Prelude

%language ElabReflection
%default total

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

public export
data Protocol : Type where
  IPPROTO_IP   : Protocol
  IPPROTO_IPV6 : Protocol
  IPPROTO_ICMP : Protocol
  IPPROTO_RAW  : Protocol
  IPPROTO_TCP  : Protocol
  IPPROTO_UDP  : Protocol

%runElab derive "Protocol" [Show,Eq]

public export
familyCode : SockFamily -> Bits32
familyCode AF_INET   = 2
familyCode AF_INET6  = 10
familyCode AF_UNIX   = 1
familyCode AF_UNSPEC = 0

public export
sockCode : SockType -> Bits32
sockCode Stream = 1
sockCode Datagram = 2
sockCode Raw = 3
sockCode Any = 0

public export
protocolCode : Protocol -> Bits32
protocolCode IPPROTO_IP   = 0
protocolCode IPPROTO_IPV6 = 41
protocolCode IPPROTO_ICMP = 1
protocolCode IPPROTO_RAW  = 255
protocolCode IPPROTO_TCP  = 6
protocolCode IPPROTO_UDP  = 17

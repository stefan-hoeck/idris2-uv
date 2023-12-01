#!/usr/bin/env bash

make -C codegen all
codegen/error_gen > src/System/UV/Data/Error.idr

cat > src/System/UV/Data/RunMode.idr << EOT
module System.UV.Data.RunMode

import Derive.Prelude

%language ElabReflection
%default total

public export
data RunMode : Type where
  Default : RunMode
  Once    : RunMode
  NoWait  : RunMode

%runElab derive "RunMode" [Show,Eq]

export
toCode : RunMode -> Bits32
EOT

codegen/run_mode_gen >> src/System/UV/Data/RunMode.idr

cat > src/System/UV/Data/Pointer.idr << EOT
module System.UV.Data.Pointer

%default total
EOT

codegen/size_gen >> src/System/UV/Data/Pointer.idr

cat > src/System/UV/Data/DNS.idr << EOT
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
EOT

codegen/dns_gen >> src/System/UV/Data/DNS.idr

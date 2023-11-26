module System.UV.TCP

import System.UV.Error
import System.UV.Pointer
import public System.UV.Raw.TCP

%default total

||| Convert a binary structure containing an IPv4 address to a string.
export
ip4name : Ptr SockAddrIn -> UVIO String
ip4name p = do
  cs <- mallocPtrs Char 256
  r  <- uv_ip4_name p cs 255
  let res = getString cs
  freePtr cs
  pure res

||| Convert a binary structure containing an IPv6 address to a string.
export
ip6name : Ptr SockAddrIn6 -> UVIO String
ip6name p = do
  cs <- mallocPtrs Char 256
  r  <- uv_ip6_name p cs 255
  let res = getString cs
  freePtr cs
  pure res

||| Convert a binary structure containing an IPv4 address or an
||| IPv6 address to a string.
export
ipname : Ptr SockAddr -> UVIO String
ipname p = do
  cs <- mallocPtrs Char 256
  r  <- uv_ip_name p cs 255
  let res = getString cs
  freePtr cs
  pure res

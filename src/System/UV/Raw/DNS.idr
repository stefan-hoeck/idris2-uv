module System.UV.Raw.DNS

import System.UV.Raw.Handle
import System.UV.Raw.Pointer
import System.UV.Raw.Loop
import System.UV.Raw.Util

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_set_ai_family")
prim__uv_set_ai_family : Ptr AddrInfo -> Int32 -> PrimIO ()

%foreign (idris_uv "uv_set_ai_socktype")
prim__uv_set_ai_socktype : Ptr AddrInfo -> Int32 -> PrimIO ()

%foreign (idris_uv "uv_set_ai_protocol")
prim__uv_set_ai_protocol : Ptr AddrInfo -> Int32 -> PrimIO ()

%foreign (idris_uv "uv_set_ai_flags")
prim__uv_set_ai_flags : Ptr AddrInfo -> Int32 -> PrimIO ()

%foreign (idris_uv "uv_get_ai_family")
prim__uv_get_ai_family : Ptr AddrInfo -> PrimIO Int32

%foreign (idris_uv "uv_get_ai_socktype")
prim__uv_get_ai_socktype : Ptr AddrInfo -> PrimIO Int32

%foreign (idris_uv "uv_get_ai_protocol")
prim__uv_get_ai_protocol : Ptr AddrInfo -> PrimIO Int32

%foreign (idris_uv "uv_get_ai_flags")
prim__uv_get_ai_flags : Ptr AddrInfo -> PrimIO Int32

%foreign (idris_uv "uv_get_ai_addr")
prim__uv_get_ai_addr : Ptr AddrInfo -> PrimIO (Ptr SockAddr)

%foreign (idris_uv "uv_freeaddrinfo")
prim__uv_freeaddrinfo : Ptr AddrInfo -> PrimIO ()

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
prim__uv_getaddrinfo :
     Ptr LoopPtr
  -> Ptr GetAddrInfo
  -> (Ptr GetAddrInfo -> Int32 -> Ptr AddrInfo -> PrimIO ())
  -> (node, service : String)
  -> (hints : Ptr AddrInfo)
  -> PrimIO Int32

%foreign (idris_uv "uv_getnameinfo")
prim__uv_getnameinfo :
     Ptr LoopPtr
  -> Ptr GetNameInfo
  -> (Ptr GetAddrInfo -> Int32 -> (hostname, servie : Ptr Char) -> PrimIO ())
  -> Ptr SockAddr
  -> (flags : Int32)
  -> PrimIO Int32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

parameters {auto has : HasIO io}

  export %inline
  uv_set_ai_family : Ptr AddrInfo -> Int32 -> io ()
  uv_set_ai_family p f = primIO $ prim__uv_set_ai_family p f

  export %inline
  uv_set_ai_socktype : Ptr AddrInfo -> Int32 -> io ()
  uv_set_ai_socktype p s = primIO $ prim__uv_set_ai_socktype p s

  export %inline
  uv_set_ai_protocol : Ptr AddrInfo -> Int32 -> io ()
  uv_set_ai_protocol p v = primIO $ prim__uv_set_ai_protocol p v
  
  export %inline
  uv_set_ai_flags : Ptr AddrInfo -> Int32 -> io ()
  uv_set_ai_flags p v = primIO $ prim__uv_set_ai_flags p v

  export %inline
  uv_get_ai_family : Ptr AddrInfo -> io Int32
  uv_get_ai_family p = primIO $ prim__uv_get_ai_family p

  export %inline
  uv_get_ai_socktype : Ptr AddrInfo -> io Int32
  uv_get_ai_socktype p = primIO $ prim__uv_get_ai_socktype p

  export %inline
  uv_get_ai_protocol : Ptr AddrInfo -> io Int32
  uv_get_ai_protocol p = primIO $ prim__uv_get_ai_protocol p
  
  export %inline
  uv_get_ai_flags : Ptr AddrInfo -> io Int32
  uv_get_ai_flags p = primIO $ prim__uv_get_ai_flags p

  export %inline
  uv_get_ai_addr : Ptr AddrInfo -> io (Ptr SockAddr)
  uv_get_ai_addr p = primIO $ prim__uv_get_ai_addr p

  export %inline
  uv_freeaddrinfo : Ptr AddrInfo -> io ()
  uv_freeaddrinfo p = primIO $ prim__uv_freeaddrinfo p

  export %inline
  uv_getaddrinfo :
       Ptr LoopPtr
    -> Ptr GetAddrInfo
    -> (Ptr GetAddrInfo -> Int32 -> Ptr AddrInfo -> IO ())
    -> (node, service : String)
    -> (hints : Ptr AddrInfo)
    -> io Int32
  uv_getaddrinfo l pa cb n s h =
    primIO $ prim__uv_getaddrinfo l pa (\x,y,z => toPrim (cb x y z)) n s h

  export %inline
  uv_getnameinfo :
       Ptr LoopPtr
    -> Ptr GetNameInfo
    -> (Ptr GetAddrInfo -> Int32 -> (hostname, service : Ptr Char) -> IO ())
    -> Ptr SockAddr
    -> (flags : Int32)
    -> io Int32
  uv_getnameinfo l pa cb sa flags =
    primIO $ prim__uv_getnameinfo l pa (\a,x,h,s => toPrim $ cb a x h s) sa flags

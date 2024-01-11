module System.UV.Raw.DNS

import System.UV.Raw.Callback
import System.UV.Raw.Handle
import System.UV.Raw.Loop
import System.UV.Raw.Pointer
import System.UV.Raw.Req
import System.UV.Raw.Util

import public System.UV.Data.DNS

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_set_ai_family")
prim__uv_set_ai_family : Ptr AddrInfo -> Bits32 -> PrimIO ()

%foreign (idris_uv "uv_set_ai_socktype")
prim__uv_set_ai_socktype : Ptr AddrInfo -> Bits32 -> PrimIO ()

%foreign (idris_uv "uv_set_ai_protocol")
prim__uv_set_ai_protocol : Ptr AddrInfo -> Bits32 -> PrimIO ()

%foreign (idris_uv "uv_set_ai_flags")
prim__uv_set_ai_flags : Ptr AddrInfo -> Bits32 -> PrimIO ()

%foreign (idris_uv "uv_get_ai_family")
prim__uv_get_ai_family : Ptr AddrInfo -> PrimIO Bits32

%foreign (idris_uv "uv_get_ai_socktype")
prim__uv_get_ai_socktype : Ptr AddrInfo -> PrimIO Bits32

%foreign (idris_uv "uv_get_ai_protocol")
prim__uv_get_ai_protocol : Ptr AddrInfo -> PrimIO Bits32

%foreign (idris_uv "uv_get_ai_flags")
prim__uv_get_ai_flags : Ptr AddrInfo -> PrimIO Bits32

%foreign (idris_uv "uv_get_ai_addr")
prim__uv_get_ai_addr : Ptr AddrInfo -> PrimIO (Ptr SockAddr)

%foreign (idris_uv "uv_freeaddrinfo")
prim__uv_freeaddrinfo : Ptr AddrInfo -> PrimIO ()

%foreign (idris_uv "uv_getaddrinfo")
prim__uv_getaddrinfo :
     Ptr Loop
  -> Ptr GetAddrInfo
  -> AnyPtr
  -> (node, service : String)
  -> (hints : Ptr AddrInfo)
  -> PrimIO Int32

%foreign (idris_uv "uv_getnameinfo")
prim__uv_getnameinfo :
     Ptr Loop
  -> Ptr GetNameInfo
  -> AnyPtr
  -> Ptr SockAddr
  -> (flags : Int32)
  -> PrimIO Int32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

parameters {auto has : HasIO io}

  export %inline
  uv_set_ai_family : Ptr AddrInfo -> Bits32 -> io ()
  uv_set_ai_family p f = primIO $ prim__uv_set_ai_family p f

  export %inline
  uv_set_ai_socktype : Ptr AddrInfo -> Bits32 -> io ()
  uv_set_ai_socktype p s = primIO $ prim__uv_set_ai_socktype p s

  export %inline
  uv_set_ai_protocol : Ptr AddrInfo -> Bits32 -> io ()
  uv_set_ai_protocol p v = primIO $ prim__uv_set_ai_protocol p v

  export %inline
  uv_set_ai_flags : Ptr AddrInfo -> Bits32 -> io ()
  uv_set_ai_flags p v = primIO $ prim__uv_set_ai_flags p v

  export %inline
  uv_get_ai_family : Ptr AddrInfo -> io Bits32
  uv_get_ai_family p = primIO $ prim__uv_get_ai_family p

  export %inline
  uv_get_ai_socktype : Ptr AddrInfo -> io Bits32
  uv_get_ai_socktype p = primIO $ prim__uv_get_ai_socktype p

  export %inline
  uv_get_ai_protocol : Ptr AddrInfo -> io Bits32
  uv_get_ai_protocol p = primIO $ prim__uv_get_ai_protocol p

  export %inline
  uv_get_ai_flags : Ptr AddrInfo -> io Bits32
  uv_get_ai_flags p = primIO $ prim__uv_get_ai_flags p

  export %inline
  uv_get_ai_addr : Ptr AddrInfo -> io (Ptr SockAddr)
  uv_get_ai_addr p = primIO $ prim__uv_get_ai_addr p

  export %inline
  uv_freeaddrinfo : Ptr AddrInfo -> io ()
  uv_freeaddrinfo p = primIO $ prim__uv_freeaddrinfo p

  export %inline
  uv_getaddrinfo :
       Ptr Loop
    -> (Ptr GetAddrInfo -> Int32 -> Ptr AddrInfo -> IO ())
    -> (node, service : String)
    -> (hints : Ptr AddrInfo)
    -> io Int32
  uv_getaddrinfo l act n s h = do
    pa <- mallocPtr GetAddrInfo
    cb <- ptrIntPtrCB (\x,y,z => act x y z >> freeReq x)
    uv_req_set_data pa cb
    primIO $ prim__uv_getaddrinfo l pa cb n s h

  export %inline
  uv_getnameinfo :
       Ptr Loop
    -> (Ptr GetAddrInfo -> Int32 -> (hostname, service : Ptr Char) -> IO ())
    -> Ptr SockAddr
    -> (flags : Int32)
    -> io Int32
  uv_getnameinfo l act sa flags = do
    pa <- mallocPtr GetNameInfo
    cb <- ptrIntPtrPtrCB (\w,x,y,z => act w x y z >> freeReq w)
    uv_req_set_data pa cb
    primIO $ prim__uv_getnameinfo l pa cb sa flags

module System.UV.Raw.TCP

import System.UV.Raw.Handle
import System.UV.Raw.Pointer
import System.UV.Raw.Loop
import System.UV.Raw.Util

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_tcp_init")
prim__uv_tcp_init : Ptr LoopPtr -> Ptr Tcp -> PrimIO Int32

%foreign (idris_uv "uv_tcp_keepalive")
prim__uv_tcp_keepalive : Ptr Tcp -> Int32 -> Bits32 -> PrimIO Int32

%foreign (idris_uv "uv_tcp_simultaneous_accepts")
prim__uv_tcp_simultaneous_accepts : Ptr Tcp -> Int32 -> PrimIO Int32

%foreign (idris_uv "uv_tcp_bind")
prim__uv_tcp_bind : Ptr Tcp -> Ptr SockAddr -> Bits32 -> PrimIO Int32

%foreign (idris_uv "uv_tcp_getsocketname")
prim__uv_tcp_getsocketname : Ptr Tcp -> Ptr SockAddr -> Int32 -> PrimIO Int32

%foreign (idris_uv "uv_tcp_getpeername")
prim__uv_tcp_getpeername : Ptr Tcp -> Ptr SockAddr -> Int32 -> PrimIO Int32

%foreign (idris_uv "uv_tcp_connect")
prim__uv_tcp_connect :
     Ptr Connect
  -> Ptr Tcp
  -> Ptr SockAddr
  -> (Ptr Connect -> Int32 -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_ip4_addr")
prim__uv_ip4_addr : String -> Bits16 -> Ptr SockAddrIn -> PrimIO Int32

%foreign (idris_uv "uv_ip6_addr")
prim__uv_ip6_addr : String -> Bits16 -> Ptr SockAddrIn6 -> PrimIO Int32

%foreign (idris_uv "uv_ip4_name")
prim__uv_ip4_name : Ptr SockAddrIn -> Ptr Char -> Bits32 -> PrimIO Int32

%foreign (idris_uv "uv_ip6_name")
prim__uv_ip6_name : Ptr SockAddrIn6 -> Ptr Char -> Bits32 -> PrimIO Int32

%foreign (idris_uv "uv_ip6_name")
prim__uv_ip_name : Ptr SockAddr -> Ptr Char -> Bits32 -> PrimIO Int32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

parameters {auto has : HasIO io}

  ||| Initialize the handle. No socket is created as of yet.
  export %inline
  uv_tcp_init : Ptr LoopPtr -> Ptr Tcp -> io Int32
  uv_tcp_init l p = primIO $ prim__uv_tcp_init l p

  ||| Enable / disable TCP keep-alive. delay is the initial
  ||| delay in seconds, ignored when enable is zero.
  ||| After delay has been reached, 10 successive probes,
  ||| each spaced 1 second from the previous one, will still happen.
  ||| If the connection is still lost at the end of this procedure,
  ||| then the handle is destroyed with a
  ||| UV_ETIMEDOUT error passed to the corresponding callback.
  export %inline
  uv_tcp_keepalive : Ptr Tcp -> Bool -> (delay : Bits32)-> io Int32
  uv_tcp_keepalive tcp b delay =
    primIO $ prim__uv_tcp_keepalive tcp (boolToInt32 b) delay

  ||| Enable / disable simultaneous asynchronous accept requests
  ||| that are queued by the operating system when listening for new TCP
  ||| connections.
  ||| 
  ||| This setting is used to tune a TCP server for the desired
  ||| performance. Having simultaneous accepts can significantly
  ||| improve the rate of accepting connections (which is why
  ||| it is enabled by default) but may lead to un‐
  ||| even load distribution in multi-process setups.
  export %inline
  uv_tcp_simultaneous_accepts : Ptr Tcp -> Bool -> io Int32
  uv_tcp_simultaneous_accepts tcp b =
    primIO $ prim__uv_tcp_simultaneous_accepts tcp (boolToInt32 b)

  ||| Bind the handle to an address and port. addr should point
  ||| to an initialized struct sockaddr_in or struct sockaddr_in6.
  ||| 
  ||| When the port is already taken, you can expect to see an UV_EADDRINUSE
  ||| error from uv_listen() or uv_tcp_connect(). That is, a successful call
  ||| to this function does not guarantee that the call to uv_listen() or
  ||| uv_tcp_connect() will succeed as well.
  ||| 
  ||| flags can contain UV_TCP_IPV6ONLY, in which case dual-stack support
  ||| is disabled and only IPv6 is used.
  export %inline
  uv_tcp_bind :
       {auto 0 _ : PCast t SockAddr}
    -> Ptr Tcp
    -> Ptr t
    -> (flags : Bits32)
    -> io Int32
  uv_tcp_bind tcp sa flags = primIO $ prim__uv_tcp_bind tcp (castPtr sa) flags

  ||| Establish an IPv4 or IPv6 TCP connection. Provide an initialized
  ||| TCP handle and an uninitialized uv_connect_t. addr should
  ||| point to an initialized struct sockaddr_in or struct sockaddr_in6.
  |||
  ||| On Windows if the addr is initialized to point to an
  ||| unspecified address (0.0.0.0 or ::) it will be changed to
  ||| point to localhost.  This is done to match the behavior of Linux systems.
  |||
  ||| The callback is made when the connection has been established
  ||| or when a connection error happened.
  export %inline
  uv_tcp_connect :
       {auto 0 _ : PCast t SockAddr}
    -> Ptr Connect
    -> Ptr Tcp
    -> Ptr t
    -> (Ptr Connect -> Int32 -> IO ())
    -> io Int32
  uv_tcp_connect pc tcp sa act =
    primIO $ prim__uv_tcp_connect pc tcp (castPtr sa) $ \p,n => toPrim (act p n)

--------------------------------------------------------------------------------
-- Addresses
--------------------------------------------------------------------------------

  ||| Convert a string containing an IPv4 address to a binary structure.
  export %inline
  uv_ip4_addr : String -> Bits16 -> Ptr SockAddrIn -> io Int32
  uv_ip4_addr addr port ptr = primIO $ prim__uv_ip4_addr addr port ptr
  
  ||| Convert a string containing an IPv6 address to a binary structure.
  export %inline
  uv_ip6_addr : String -> Bits16 -> Ptr SockAddrIn6 -> io Int32
  uv_ip6_addr addr port ptr = primIO $ prim__uv_ip6_addr addr port ptr

  ||| Convert a binary structure containing an IPv4 address to a string.
  export %inline
  uv_ip4_name : Ptr SockAddrIn -> Ptr Char -> Bits32 -> io Int32
  uv_ip4_name sa str len = primIO $ prim__uv_ip4_name sa str len

  ||| Convert a binary structure containing an IPv6 address to a string.
  export %inline
  uv_ip6_name : Ptr SockAddrIn6 -> Ptr Char -> Bits32 -> io Int32
  uv_ip6_name sa str len = primIO $ prim__uv_ip6_name sa str len

  ||| Convert a binary structure containing an IPv4 address or an
  ||| IPv6 address to a string.
  export %inline
  uv_ip_name : Ptr SockAddr -> Ptr Char -> Bits32 -> io Int32
  uv_ip_name sa str len = primIO $ prim__uv_ip_name sa str len

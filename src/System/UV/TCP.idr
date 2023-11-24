module System.UV.TCP

import System.FFI
import System.UV.Error
import System.UV.Handle
import System.UV.Pointer
import System.UV.Loop
import System.UV.Req
import System.UV.Util

%default total

export
data Sock : Type where

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_tcp_init")
prim__uv_tcp_init : Ptr LoopPtr -> Ptr Tcp -> PrimIO Int32

%foreign (idris_uv "uv_tcp_open")
prim__uv_tcp_open : Ptr Tcp -> Ptr Sock -> PrimIO Int32

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

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Initialize the handle. No socket is created as of yet.
export %inline
tcpInit : (l : Loop) => Ptr Tcp -> UVIO ()
tcpInit p = primUV $ prim__uv_tcp_init l.loop p

||| Open an existing file descriptor or SOCKET as a TCP handle.
export %inline
tcpOpen : Ptr Tcp -> Ptr Sock -> UVIO ()
tcpOpen tcp sock = primUV $ prim__uv_tcp_open tcp sock

||| Enable / disable TCP keep-alive. delay is the initial
||| delay in seconds, ignored when enable is zero.
||| After delay has been reached, 10 successive probes,
||| each spaced 1 second from the previous one, will still happen.
||| If the connection is still lost at the end of this procedure,
||| then the handle is destroyed with a
||| UV_ETIMEDOUT error passed to the corresponding callback.
export %inline
tcpKeepalive : Ptr Tcp -> Bool -> (delay : Bits32)-> UVIO ()
tcpKeepalive tcp b delay =
  primUV $ prim__uv_tcp_keepalive tcp (boolToInt32 b) delay

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
tcpSimultaneousAccepts : Ptr Tcp -> Bool -> UVIO ()
tcpSimultaneousAccepts tcp b =
  primUV $ prim__uv_tcp_simultaneous_accepts tcp (boolToInt32 b)

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
tcpBind :
     {auto 0 _ : PCast t SockAddr}
  -> Ptr Tcp
  -> Ptr t
  -> (flags : Bits32)
  -> UVIO ()
tcpBind tcp sa flags = primUV $ prim__uv_tcp_bind tcp (castPtr sa) flags

-- ||| Get the current address to which the handle is bound. name must
-- ||| point to a valid and big enough chunk of memory, struct
-- ||| sockaddr_storage is recommended for IPv4 and IPv6 support.
-- export %inline
-- tcpGetSocketName :
--      {auto 0 _ : AddrCast t}
--   -> {auto has : HasIO io} 
--   -> Ptr Tcp
--   -> Ptr t
--   -> Int32
--   -> io Int32
-- tcpGetSocketName tcp sa len =
--   primIO $ prim__uv_tcp_getsocketname tcp (castAddr sa) len
-- 
-- ||| Get the address of the peer connected to the handle.
-- ||| name must point to a valid and big enough chunk of memory,
-- ||| struct sockaddr_storage is recommended for IPv4 and IPv6 support.
-- export %inline
-- tcpGetPeerName : HasIO io => Ptr Tcp -> Ptr SockAddr -> Int32 -> io Int32
-- tcpGetPeerName tcp sa len = primIO $ prim__uv_tcp_getpeername tcp sa len

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
tcpConnect :
     {auto 0 _ : PCast t SockAddr}
  -> Ptr Connect
  -> Ptr Tcp
  -> Ptr t
  -> (Ptr Connect -> Int32 -> IO ())
  -> UVIO ()
tcpConnect pc tcp sa act =
  primUV $ prim__uv_tcp_connect pc tcp (castPtr sa) $ \p,n => toPrim (act p n)

--------------------------------------------------------------------------------
-- Addresses
--------------------------------------------------------------------------------

export %inline
ip4Addr : String -> Bits16 -> Ptr SockAddrIn -> UVIO ()
ip4Addr addr port ptr = primUV $ prim__uv_ip4_addr addr port ptr

export %inline
ip6Addr : String -> Bits16 -> Ptr SockAddrIn6 -> UVIO ()
ip6Addr addr port ptr = primUV $ prim__uv_ip6_addr addr port ptr

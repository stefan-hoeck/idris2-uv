module System.UV.TCP

import System.UV.Loop
import System.UV.Pointer
import System.UV.Raw.Stream
import public System.UV.Raw.TCP

%default total

-- ||| Convert a binary structure containing an IPv4 address to a string.
-- export
-- ip4name : Ptr SockAddrIn -> IO String
-- ip4name p = do
--   cs <- mallocPtrs Char 256
--   r  <- uv_ip4_name p cs 255
--   let res = getString cs
--   freePtr cs
--   pure res
--
-- ||| Convert a binary structure containing an IPv6 address to a string.
-- export
-- ip6name : Ptr SockAddrIn6 -> IO String
-- ip6name p = do
--   cs <- mallocPtrs Char 256
--   r  <- uv_ip6_name p cs 255
--   let res = getString cs
--   freePtr cs
--   pure res
--
-- ||| Convert a binary structure containing an IPv4 address or an
-- ||| IPv6 address to a string.
-- export
-- ipname : Ptr SockAddr -> IO String
-- ipname p = do
--   cs <- mallocPtrs Char 256
--   r  <- uv_ip_name p cs 255
--   let res = getString cs
--   freePtr cs
--   pure res
--
-- export
-- tcpListen :
--      {auto l : UVLoop}
--   -> (addresss : String)
--   -> (port     : Bits16)
--   -> Source [UVError] (Ptr Stream)
-- tcpListen address port = MkSource $ do
--   server <- mallocPtr Tcp
--   addr   <- mallocPtr SockAddrIn
--   ref    <- sourceRef [UVError] (Ptr Stream)
--               (releaseHandle server >> freePtr addr)
--
--   r1     <- uv_tcp_init l.loop server
--
--   -- binding the server to local address 0.0.0.0 at port 7000
--   r2     <- uv_ip4_addr address port addr
--   r3     <- uv_tcp_bind server addr 0
--
--   r4     <- uv_listen server 128 $ \p,res =>
--               case uvRes res of
--                 Left err => error ref err
--                 Right () => emit1 ref p
--   case traverse_ uvRes [r1,r2,r3,r4] of
--     Left err => error ref err
--     Right () => pure ()
--
--   pure $ hotSrc ref

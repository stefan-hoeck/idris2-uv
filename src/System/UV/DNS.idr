module System.UV.DNS

import System.Rx

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

public export
record SockInfo where
  constructor SI
  family   : SockFamily
  type     : SockType
  protocol : Protocol

%inline gaCB :
     Ptr AddrInfo
  -> (Either UVError (IO (), Ptr AddrInfo) -> IO ())
  -> Ptr GetAddrInfo
  -> Int32
  -> Ptr AddrInfo
  -> IO ()
gaCB hints cb pg st pa = do
  freePtr hints
  freePtr pg
  case uvRes st of
    Left err => uv_freeaddrinfo pa >> cb (Left err)
    Right () => cb $ Right (uv_freeaddrinfo pa, pa)

hints : SockInfo -> IO (Ptr AddrInfo)
hints (SI f t p) = do
  hs <- mallocPtr AddrInfo
  uv_set_ai_family   hs (familyCode f)
  uv_set_ai_socktype hs (sockCode t)
  uv_set_ai_protocol hs (protocolCode p)
  pure hs

export %inline
getAddrInfo :
     {auto l : UVLoop}
  -> (node, service : String)
  -> SockInfo
  -> (Either UVError (IO (), Ptr AddrInfo) -> IO ())
  -> IO ()
getAddrInfo n s h cb = do
  hs  <- hints h
  pg <- mallocPtr GetAddrInfo
  res <- uv_getaddrinfo l.loop pg (gaCB hs cb) n s hs
  case uvRes res of
    Left err => freePtr hs >> freePtr pg >> (cb $ Left err)
    Right _  => pure ()

export %inline
addrInfo :
     {auto l : UVLoop}
  -> (node, service : String)
  -> SockInfo
  -> Source [UVError] (IO (), Ptr AddrInfo)
addrInfo n s h = MkSource $ do
  ref <- sourceRef [UVError] (IO (), Ptr AddrInfo) (pure ())
  pure $ coldSrc ref $ \cb => getAddrInfo n s h $ \case
    Left err => cb (Err $ inject err)
    Right p  => cb (Done [p])

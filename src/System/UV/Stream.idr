module System.UV.Stream

import Data.Buffer.Indexed
import Data.ByteString

import System.Rx
import System.UV.Error
import System.UV.Handle
import System.UV.Pointer
import System.UV.Loop
import public System.UV.Raw.Stream

%default total

toMsg : Int32 -> Ptr Buf -> IO (Msg [UVError] ByteString)
toMsg n buf =
  case uvRes n $> n of
    Left EOF => pure (Done [])
    Left err => pure (Err $ inject err)
    Right n  => Next . pure <$> toByteString buf (cast n)

export
streamRead :
     {auto l : UVLoop}
  -> (buffer : Bits32)
  -> Ptr t
  -> IO ()
  -> {auto 0 cstt : PCast t Stream}
  -> Source [UVError] ByteString
streamRead buffer h cleanup = MkSource $ do
  cs  <- mallocPtrs Bits8 buffer
  ref <- sourceRef [UVError] ByteString (cleanup >> freePtr cs)
  r   <- uv_read_start h (\_,_,b => initBuf b cs buffer) (\_,n,b => toMsg n b >>= send ref)
  case uvRes r of
    Left e   => error ref e
    Right () => pure ()
  pure $ hotSrc ref

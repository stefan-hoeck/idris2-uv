module System.UV.Pointer

import IO.Async
import Data.Buffer.Indexed
import Data.ByteString
import System.FFI
import System.UV.Util

import public System.UV.Raw.Pointer

%default total

export %inline
Resource (Ptr Bits8) where
  release = freePtr

export %inline
Resource (Ptr Char) where
  release = freePtr

--------------------------------------------------------------------------------
-- String Conversions
--------------------------------------------------------------------------------

||| Reads `n` bytes of data from the byte array in a `uv_buf_t`
||| into an Idris-managed immutable `ByteString`
export
toByteString : HasIO io => Ptr Buf -> Bits32 -> io ByteString
toByteString p x = do
  buf <- newBuffer x
  copyToBuffer p buf x
  pure $ unsafeByteString (cast x) buf

||| Reads `n` bytes of data from the byte array in a `uv_buf_t`
||| into an Idris-managed string.
export %inline
toString : HasIO io => Ptr Buf -> Bits32 -> io String
toString p s = toString <$> toByteString p s

-- ||| Allocates a `uv_buf_t` to hold the data in the given bytestring.
-- export
-- fromByteString : HasIO io => ByteString -> io (Ptr Buf)
-- fromByteString bs = do
--   buf <- liftIO $ toBuffer bs
--   ptr <- mallocBuf (cast bs.size)
--   copyFromBuffer buf ptr (cast bs.size)
--   pure ptr
--
-- ||| Allocates a `uv_buf_t` to hold the data in the given bytestring.
-- export %inline
-- fromString : HasIO io => String -> io (Ptr Buf)
-- fromString = fromByteString . fromString

module System.UV.Pointer

import IO.Async
import Data.Buffer
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
toByteString : HasIO io => Ptr Bits8 -> Bits32 -> io ByteString
toByteString p x = do
  buf <- newBuffer x
  copyToBuffer p buf x
  pure $ unsafeByteString (cast x) buf

export
bufToByteString : HasIO io => Ptr Buf -> Bits32 -> io ByteString
bufToByteString p x = getBufBase p >>= \y => toByteString y x

||| Reads `n` bytes of data from the byte array in a `uv_buf_t`
||| into an Idris-managed string.
export %inline
toString : HasIO io => Ptr Bits8 -> Bits32 -> io String
toString p s = toString <$> toByteString p s

||| Allocates a byte array to hold the data in the given bytestring.
export
fromByteString : HasIO io => ByteString -> io (Ptr Bits8)
fromByteString (BS s (BV b o _)) =
  copyFromBuffer (unsafeGetBuffer b) (cast s) (cast o)

||| Allocates a byte array to hold the data in the given bytestring.
export %inline
fromString : HasIO io => String -> io (Ptr Bits8)
fromString = fromByteString . fromString

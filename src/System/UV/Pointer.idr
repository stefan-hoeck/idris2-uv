module System.UV.Pointer

import Data.Buffer.Indexed
import Data.ByteString
import System.FFI
import System.UV.Util

import public System.UV.Raw.Pointer

%default total

--------------------------------------------------------------------------------
-- String Conversions
--------------------------------------------------------------------------------

||| Convert a `Ptr Char` to an Idris string.
|||
||| Note: Users must make sure that the given pointer points at a
||| zero-terminated byte array. As an alternative, consider converting
||| a `Ptr Bits8`.
export %inline
getString : Ptr Char -> String
getString p = prim__getString (believe_me p)

||| Like `getString` but returns `Nothing` in case the given pointer is the
||| null pointer.
export %inline
getStringMay : Ptr Char -> Maybe String
getStringMay p =
  case prim__nullPtr p of
    0 => Just $ getString p
    _ => Nothing

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

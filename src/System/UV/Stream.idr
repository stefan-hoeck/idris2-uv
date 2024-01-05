module System.UV.Stream

import Data.Buffer.Indexed
import Data.ByteString

import System.UV.Loop
import System.UV.Pointer
import System.UV.Raw.Handle
import public System.UV.Raw.Stream

%default total

public export
data ReadRes : (a : Type) -> Type where
  Done : ReadRes a
  Data : (val : a) -> ReadRes a
  Err  : UVError -> ReadRes a

toMsg : Int32 -> Ptr Buf -> IO (ReadRes ByteString)
toMsg n buf =
  case uvRes {es = [UVError]} n $> n of
    Left (Here EOF) => pure Done
    Left (Here err) => pure (Err err)
    Right n         => Data <$> toByteString buf (cast n)

-- parameters {auto l : UVLoop}
--            {auto has : Has UVError es}
--
--   export
--   streamRead :
--        (buffer : Bits32)
--     -> Ptr t
--     -> {auto 0 cstt : PCast t Stream}
--     -> {auto res    : Resource (Ptr t)}
--     -> (Cancel -> ReadRes ByteString -> Async [] ())
--     -> Async es Cancel
--   streamRead buffer h run = do
--     cs  <- mallocPtrs Bits8 buffer
--     ccl <- mkCancel (release cs >> uv_read_stop h)
--     uvPar ccl (run ccl) $ \cb =>
--       uv_read_start
--         h
--         (\_,_,b => initBuf b cs buffer)
--         (\_,n,buf => toMsg n buf >>= cb)

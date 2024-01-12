module System.UV.Stream

import Data.Buffer.Indexed
import Data.ByteString

import System.UV.Loop
import System.UV.Pointer
import System.UV.Raw.Handle
import System.UV.Raw.Stream

%default total

export %inline
Resource AllocCB where
  release = freeAllocCB

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
    Right n         => Data <$> bufToByteString buf (cast n)

export
(cc : CloseCB) => Resource (Ptr Stream) where
  release h = uv_close h cc

parameters {auto l : UVLoop}
           {auto has : Has UVError es}

  export covering
  streamRead :
       AllocCB
    -> Ptr t
    -> {auto 0 cstt : PCast t Stream}
    -> (ReadRes ByteString -> Async es (Maybe a))
    -> Async es (Fiber es a)
  streamRead ac h run = do
    uvForever run h (\x => uv_read_stop x) $ \cb =>
      uv_read_start h ac (\_,n,buf => toMsg n buf >>= cb)

  export covering
  write :
       Ptr t
    -> {auto 0 cstt : PCast t Stream}
    -> ByteString
    -> Async es ()
  write str b =
    use1 (fromByteString b) $ \cs =>
      uv $ uv_write str cs (cast b.size) (\_,_ => pure ())

  export covering
  listen :
       Ptr t
    -> {auto 0 cstt : PCast t Stream}
    -> (Either UVError (Ptr Stream) -> Async es (Maybe a))
    -> Async es (Fiber es a)
  listen server run =
    uvForever run server (\_ => pure ()) $ \cb =>
      uv_listen server 128 $ \p,res =>
        cb $ if res < 0 then Left $ fromCode res else Right p

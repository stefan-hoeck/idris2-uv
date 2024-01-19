module System.UV.Stream

import Data.Buffer.Indexed
import Data.ByteString

import IO.Async.MVar

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

  close_stream : Ptr Stream -> Async [] ()
  close_stream x = do
    uv_read_stop x
    ignore (uv_shutdown x $ \_,_ => uv_close x %search)

  export
  read :
       AllocCB
    -> Ptr t
    -> {auto 0 cstt : PCast t Stream}
    -> (MBuffer (ReadRes ByteString) -> Async es a)
    -> Async es a
  read {a} ac h run = finally act (uv_read_stop h)
    where
      act : Async es a
      act = do
        st <- liftIO newMBuffer
        uv $ uv_read_start h ac (\_,n,buf => toMsg n buf >>= store st)
        run st

  export
  write : Ptr t -> (0 _ : PCast t Stream) => ByteString -> Async es ()
  write str b =
    use1 (fromByteString b) $ \cs =>
      uv $ uv_write str cs (cast b.size) (\_,_ => pure ())

  -- export
  -- listen :
  --      Ptr t
  --   -> {auto 0 cst : PCast t Stream}
  --   -> (MQueue (Either UVError $ Ptr Stream) -> Async es a)
  --   -> Async es a
  -- listen {a} {cst} server run = do
  --   q <- newMQueue
  --   uv_listen server 128 $ \p,res =>
  --     enqueue q (uvCheck res p)if res < 0 then Left $ fromCode res else Right p

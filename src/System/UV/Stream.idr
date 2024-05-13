module System.UV.Stream

import Control.Monad.Trans
import Data.Buffer.Indexed
import Data.ByteString

import IO.Async.Event

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

export
Functor ReadRes where
  map _ Done       = Done
  map f (Data val) = Data (f val)
  map _ (Err err)  = Err err

export
Applicative ReadRes where
  pure = Data

  Data f  <*> Data a  = pure (f a)
  Done    <*> _       = Done
  Err err <*> _       = Err err
  _       <*> Done    = Done
  _       <*> Err err = Err err

export
Monad ReadRes where
  Done    >>= _ = Done
  Data a  >>= f = f a
  Err err >>= _ = Err err

public export
data ReadResT : (m : Type -> Type) -> (a : Type) -> Type where
  MkReadResT : m (ReadRes a) -> ReadResT m a

export %inline
runReadResT : ReadResT m a -> m (ReadRes a)
runReadResT (MkReadResT x) = x

export
Functor m => Functor (ReadResT m) where
  map f (MkReadResT x) = MkReadResT $ map f <$> x

export
Applicative m => Applicative (ReadResT m) where
  pure = MkReadResT . pure . pure
  MkReadResT f <*> MkReadResT x = MkReadResT [| f <*> x |]

export
Monad m => Monad (ReadResT m) where
  MkReadResT x >>= f = MkReadResT $ do
    Data x' <- x | Err err => pure (Err err)
                 | Done => pure Done
    runReadResT $ f x'

export
MonadTrans ReadResT where
  lift = MkReadResT . map pure

export
HasIO m => HasIO (ReadResT m) where
  liftIO act = MkReadResT $ liftIO act >>= pure . pure

toMsg : Int32 -> Ptr Buf -> IO (ReadRes ByteString)
toMsg n buf =
  case uvRes {es = [UVError]} n $> n of
    Left (Here EOF) => pure Done
    Left (Here err) => pure (Err err)
    Right n         => Data <$> bufToByteString buf (cast n)

export
(cc : CloseCB) => Resource (Ptr Stream) where
  release h = uv_close h cc

export
shutdownStream : UVLoop => (0 pc : PCast t Stream) => Ptr t -> Async [] ()
shutdownStream x =
  let s := castPtr @{pc} x
   in uv_read_stop s >> ignore (uv_shutdown s $ \_,_ => release s)

parameters {auto l : UVLoop}
           {auto has : Has UVError es}

  export
  read :
       AllocCB
    -> Ptr t
    -> {auto 0 cstt : PCast t Stream}
    -> (Buffer (ReadRes ByteString) -> Async es a)
    -> Async es a
  read {a} ac h run = finally act (uv_read_stop h)
    where
      act : Async es a
      act = do
        st <- newEvent
        uv $ uv_read_start h ac (\_,n,buf => toMsg n buf >>= buffer st)
        run st

  export
  write : Ptr t -> (0 _ : PCast t Stream) => ByteString -> Async es ()
  write str b =
    use1 (fromByteString b) $ \cs => uvAsync $ \cb =>
      uv_write str cs (cast b.size) (\_,_ => cb $ Succeeded ())

  export
  listen :
       Ptr t
    -> {auto 0 cst : PCast t Stream}
    -> (Buffer (Either UVError $ Ptr Stream) -> Async es a)
    -> Async es a
  listen {a} {cst} server run = do
    q <- newEvent
    uv $ uv_listen server 128 $ \p,res =>
      buffer q $ if res < 0 then Left $ fromCode res else Right p
    run q

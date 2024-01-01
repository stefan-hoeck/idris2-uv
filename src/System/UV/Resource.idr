module System.UV.Resource

import Data.IORef
import System.UV.Async
import System.UV.Loop
import System.UV.Raw.Handle
import System.UV.Raw.Pointer

%default total

export
uvAsync : Has UVError es => ((Outcome es a -> IO ()) -> IO Int32) -> Async es a
uvAsync f =
  AS $ \cb => do
    res <- f cb
    case uvRes res of
      Left err => cb (Left err)
      Right () => pure ()

export
uv : Has UVError es => IO Int32 -> Async es ()
uv = sync . map uvRes

public export
interface Resource a where
  release : HasIO io => a -> io ()

export
Resource (Ptr Idle) where
  release h = uv_close h freePtr

export
Resource (Ptr Check) where
  release h = uv_close h freePtr

export
Resource (Ptr Prepare) where
  release h = uv_close h freePtr

export
Resource (Ptr Signal) where
  release h = uv_close h freePtr

export
Resource (Ptr Timer) where
  release h = uv_close h freePtr

export
Resource (Ptr Buf) where
  release = freeBuf

export
Resource (Ptr Bits8) where
  release = freePtr

export
Resource (Ptr Char) where
  release = freePtr

export
use :
     {auto rs : All Resource ts}
  -> All (Async es) ts
  -> (HList ts -> Async es a)
  -> Async es a
use []                  f = f []
use @{_ :: _} (v :: vs) f = do
  rv <- v
  finally (use vs $ f . (rv::)) (release rv)

--------------------------------------------------------------------------------
-- Cancel
--------------------------------------------------------------------------------

export
record Cancel where
  constructor C
  ref : IORef (IO ())

export
mkCancel : HasIO io => IO () -> io Cancel
mkCancel = map C . newIORef

export
cancel : HasIO io => Cancel -> io ()
cancel (C r) =
  liftIO $ do
    io <- readIORef r
    writeIORef r (pure ())
    io

--------------------------------------------------------------------------------
-- libuv interop
--------------------------------------------------------------------------------

export
uvAct : Has UVError es => Resource a => (a -> IO Int32) -> a -> Async es a
uvAct f v = onErr' (uv $ f v) (release v) $> v

||| Registers a callback at the libuv loop to be run continuously.
export
uvPar :
     {auto has : Has UVError es}
  -> Cancel
  -> (a -> Async [] ())
  -> ((a -> IO ()) -> IO Int32)
  -> Async es Cancel
uvPar res fun reg = onErr' (uv (reg $ run . fun) $> res) (cancel res)

||| Registers a callback at the libuv loop to be run continuously.
export
uvPar' :
     {auto has : Has UVError es}
  -> Cancel
  -> Async [] ()
  -> (IO () -> IO Int32)
  -> Async es Cancel
uvPar' res fun reg = onErr' (uv (reg $ run fun) $> res) (cancel res)

||| Registers a callback at the libuv loop to be run once.
export
uvPar1 :
     {auto has : Has UVError es}
  -> Cancel
  -> (a -> Async [] ())
  -> ((a -> IO ()) -> IO Int32)
  -> Async es Cancel
uvPar1 res fun reg = uvPar res (\va => cancel res >> fun va) reg

||| Registers a callback at the libuv loop to be run once.
export
uvPar1' :
     {auto has : Has UVError es}
  -> Cancel
  -> Async [] ()
  -> (IO () -> IO Int32)
  -> Async es Cancel
uvPar1' res fun reg = uvPar' res (cancel res >> fun) reg

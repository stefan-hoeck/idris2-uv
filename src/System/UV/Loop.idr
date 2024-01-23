module System.UV.Loop

import IO.Async.MVar
import IO.Async.Token

import Data.IORef
import System
import System.UV.Raw.Async
import System.UV.Raw.Handle
import System.UV.Raw.Loop
import System.UV.Raw.Pointer

import public IO.Async
import public System.UV.Data.Error
import public System.UV.Data.RunMode

%default total

public export
record UVLoop where
  [noHints]
  constructor MkLoop
  loop  : Ptr Loop
  async : Ptr Async
  tg    : TokenGen
  cc    : CloseCB
  ref   : IORef (SnocList $ IO ())
  limit : Nat

export %inline %hint
loopCtxt : UVLoop => ExecutionContext
loopCtxt @{l} =
  EC
    l.tg
    (\x => modifyIORef l.ref (:< x) >> ignore (uv_async_send l.async))
    l.limit

export %inline %hint
loopCloseCB : UVLoop => CloseCB
loopCloseCB @{l} = l.cc

||| Returns the default loop, corresponding to `uv_default_loop`.
export
defaultLoop : IO UVLoop
defaultLoop = do
  l   <- uv_default_loop
  tg  <- newTokenGen
  ref <- newIORef {a = SnocList $ IO ()} [<]
  cc  <- defaultClose
  pa  <- mallocPtr Async

  let loop := MkLoop l pa tg cc ref 100

  r2  <- uv_async_init l pa $ \x => do
           ss <- readIORef ref
           writeIORef ref [<]
           sequence_ (ss <>> [])
  pure loop

parameters {auto has : Has UVError es}

  export
  uvCheck : a -> Int32 -> Result es a
  uvCheck v n = if n < 0 then Left (inject $ fromCode n) else Right v

  export %inline
  uvRes : Int32 -> Result es ()
  uvRes = uvCheck ()

  export
  uv : IO Int32 -> Async es ()
  uv = sync . map uvRes

  export
  uvAct : Resource a => (a -> IO Int32) -> a -> Async es a
  uvAct f v = onAbort (uv $ f v) (release v) $> v

  export
  uvCancelableAsync :
       (ptr : Async es r)
    -> (cancel : r -> Async [] ())
    -> (free   : r -> Async [] ())
    -> (r -> (a -> IO ()) -> IO Int32)
    -> Async es a
  uvCancelableAsync ptr cancel free reg =
    bracket
      ptr
      (\p => cancelableAsync $ \cb => do
         n <- reg p (cb . Succeeded)
         case uvRes n of
           Left err => cb (Error err) $> pure ()
           Right () => pure (cancel p)
           )
      free

  export
  uvAsync : ((Outcome es a -> IO ()) -> IO Int32) -> Async es a
  uvAsync f =
    async $ \cb => do
      n <- f cb
      case uvRes n of
        Left err => cb (Error err)
        Right () => pure ()

export %inline
Resource CloseCB where
  release = freeCloseCB

||| Sets up the given application by registering it at the default loop
||| and starting the loop afterwards.
covering export
runUV : (UVLoop => Async [] ()) -> IO ()
runUV act = do
  loop <- defaultLoop
  runAsync $ finally (act @{loop}) (liftIO $ uv_close loop.async loop.cc)
  res <- uv_run loop.loop (toCode Default)
  case uvRes {es = [UVError]} res of
    Left (Here err) => die "\{err}"
    Right _         => pure ()

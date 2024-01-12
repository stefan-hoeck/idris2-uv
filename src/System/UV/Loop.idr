module System.UV.Loop

import IO.Async.CancelState
import IO.Async.MVar
import IO.Async.Token

import Data.IORef
import System
import System.UV.Raw.Handle
import System.UV.Raw.Loop
import System.UV.Raw.Pointer
import System.UV.Raw.Idle

import public IO.Async
import public System.UV.Data.Error
import public System.UV.Data.RunMode

%default total

public export
record UVLoop where
  [noHints]
  constructor MkLoop
  loop : Ptr Loop
  tg   : TokenGen
  cc   : CloseCB
  ref  : IORef (SnocList EvalST)

export %inline %hint
loopTokenGen : UVLoop => AsyncContext
loopTokenGen @{l} = AC l.tg (\x => modifyIORef l.ref (:< x))

export %inline %hint
loopCloseCB : UVLoop => CloseCB
loopCloseCB @{l} = l.cc

||| Returns the default loop, corresponding to `uv_default_loop`.
export covering
defaultLoop : IO UVLoop
defaultLoop = do
  l   <- uv_default_loop
  tg  <- newTokenGen
  ref <- newIORef {a = SnocList EvalST} [<]
  cc  <- defaultClose

  let loop := MkLoop l tg cc ref

  pc  <- mallocPtr Idle
  r1  <- uv_idle_init l pc
  r2  <- uv_idle_start pc $ \x => do
           readIORef ref >>= \case
             [<] => ignore (uv_idle_stop x) >> uv_close x cc
             ss  => writeIORef ref [<] >> traverse_ eval (ss <>> [])
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
  uv = liftEither . map uvRes

  export
  uvAct : Resource a => (a -> IO Int32) -> a -> Async es a
  uvAct f v = onAbort (uv $ f v) (release v) $> v

  export
  uvOnce :
       (ptr : r)
    -> (close : r -> Async [] ())
    -> ((a -> IO ()) -> IO Int32)
    -> Async es a
  uvOnce p close reg =
    finally
      (cancelable $ async $ \cb => do
         n <- reg (cb . Succeeded)
         case uvRes n of
           Left err => cb (Error err)
           Right () => pure ()
           )
      (close p)

  export covering
  uvOnce' :
       (ptr : r)
    -> (close : r -> Async [] ())
    -> (IO () -> IO Int32)
    -> Async es ()
  uvOnce' p close reg = uvOnce p close (\f => reg (f ()))

parameters {auto has : Has UVError es}
           {auto l   : UVLoop}

  export covering
  uvForever :
       (a -> Async es (Maybe b))
    -> (ptr : r)
    -> (close : r -> Async [] ())
    -> ((a -> IO ()) -> IO Int32)
    -> Async es (Fiber es b)
  uvForever to p close reg =
    start $ finally
      (cancelable $ forever $ \cb => do
         n <- reg (\va => onAsync (to va) cb)
         case uvRes n of
           Left err => cb (Error err)
           Right () => pure ()
           )
      (close p)

  export covering
  uvForever' :
       Async es (Maybe b)
    -> (ptr : r)
    -> (close : r -> Async [] ())
    -> (IO () -> IO Int32)
    -> Async es (Fiber es b)
  uvForever' as p close reg = uvForever (const as) p close (\f => reg (f ()))

  export
  uvAsync : ((Outcome es a -> IO ()) -> IO Int32) -> Async es a
  uvAsync f =
    async $ \cb => do
      n <- f cb
      case uvRes n of
        Left err => cb (Error err)
        Right () => pure ()

||| Sets up the given application by registering it at the default loop
||| and starting the loop afterwards.
covering export
runUV : (UVLoop => IO ()) -> IO ()
runUV act = do
  loop <- defaultLoop
  act @{loop}
  res <- uv_run loop.loop (toCode Default)
  case uvRes {es = [UVError]} res of
    Left (Here err) => die "\{err}"
    Right _         => pure ()

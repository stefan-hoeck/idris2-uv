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
  ref  : IORef (List EvalST)

export %inline %hint
loopTokenGen : UVLoop => TokenGen
loopTokenGen @{l} = l.tg

register : IORef (List a) -> a -> IO ()
register ref = modifyIORef ref . (::)

||| Returns the default loop, corresponding to `uv_default_loop`.
export covering
defaultLoop : IO UVLoop
defaultLoop = do
  l   <- uv_default_loop
  tg  <- newTokenGen
  ref <- newIORef {a = List EvalST} []
  pc  <- mallocPtr Idle
  r1  <- uv_idle_init l pc
  r2  <- uv_idle_start pc $ \x => do
           readIORef ref >>= \case
             [] => ignore (uv_idle_stop x) >> uv_close x freePtr
             ss => writeIORef ref [] >> traverse_ (eval (register ref)) ss
  pure $ MkLoop l tg ref

parameters {auto l : UVLoop}

  export covering
  onAsync : Async es a -> (Outcome es a -> IO ()) -> IO ()
  onAsync as cb = do
    fb  <- newFiber Nothing
    eval (register l.ref) (EST fb $ guarantee as (liftIO . cb))

  export covering %inline
  runAsync : Async [] () -> IO ()
  runAsync as = onAsync as (\_ => pure ())

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

  export covering
  uvForever :
       {auto l : UVLoop}
    -> (a -> Async es (Maybe b))
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
       {auto l : UVLoop}
    -> Async es (Maybe b)
    -> (ptr : r)
    -> (close : r -> Async [] ())
    -> (IO () -> IO Int32)
    -> Async es (Fiber es b)
  uvForever' as p close reg = uvForever (const as) p close (\f => reg (f ()))

  export covering
  uvOnce :
       {auto l : UVLoop}
    -> (a -> Async es b)
    -> (ptr : r)
    -> (close : r -> Async [] ())
    -> ((a -> IO ()) -> IO Int32)
    -> Async es (Fiber es b)
  uvOnce to p close reg =
    start $ finally
      (cancelable $ async $ \cb => do
         n <- reg (\va => onAsync (to va) cb)
         case uvRes n of
           Left err => cb (Error err)
           Right () => pure ()
           )
      (close p)

  export covering
  uvOnce' :
       {auto l : UVLoop}
    -> Async es b
    -> (ptr : r)
    -> (close : r -> Async [] ())
    -> (IO () -> IO Int32)
    -> Async es (Fiber es b)
  uvOnce' as p close reg = uvOnce (const as) p close (\f => reg (f ()))

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
  putStrLn "Starting event loop"
  res <- uv_run loop.loop (toCode Default)
  case uvRes {es = [UVError]} res of
    Left (Here err) => die "\{err}"
    Right _         => pure ()

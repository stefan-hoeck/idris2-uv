module System.UV.Loop

import IO.Async
import IO.Async.CancelState
import IO.Async.MVar
import IO.Async.Token

import Data.IORef
import System
import System.UV.Error
import System.UV.Raw.Handle
import System.UV.Raw.Loop
import System.UV.Raw.Pointer
import System.UV.Raw.Idle

import public System.UV.Data.RunMode

%default total

public export
record UVLoop where
  [noHints]
  constructor MkLoop
  loop : Ptr Loop
  tg   : TokenGen

export %inline %hint
loopTokenGen : UVLoop => TokenGen
loopTokenGen @{l} = l.tg

||| Returns the default loop, corresponding to `uv_default_loop`.
export %inline
defaultLoop : IO UVLoop
defaultLoop = [| MkLoop uv_default_loop newTokenGen |]

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

parameters {auto l : UVLoop}

  covering
  uvStep : IO (Maybe EvalST -> IO ())
  uvStep = do
    ref <- newIORef {a = Maybe EvalST} Nothing
    pc  <- mallocPtr Check
    r1  <- uv_check_init l.loop pc
    r2  <- uv_check_start pc $ \_ => do
             Just st <- readIORef ref
               | Nothing => ignore (uv_check_stop pc) >> uv_close pc freePtr
             eval uvStep (writeIORef ref) st
    pure (writeIORef ref)

  export covering
  onAsync : Async es a -> (Outcome es a -> IO ()) -> IO ()
  onAsync as cb = do
    fb  <- newFiber Nothing
    stp <- uvStep
    eval uvStep stp (EST fb $ guarantee as (liftIO . cb))

  export covering %inline
  runAsync : Async [] () -> IO ()
  runAsync as = onAsync as (\_ => pure ())

parameters {auto has : Has UVError es}

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
    -> Async es b
  uvForever to p close reg =
    finally
      (forever $ \cb => do
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
    -> Async es b
  uvForever' as p close reg = uvForever (const as) p close (\f => reg (f ()))

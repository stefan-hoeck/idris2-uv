module IO.Async.MVar

import Data.IORef
import Data.Queue
import System.Concurrency

%default total

--------------------------------------------------------------------------------
-- MVar
--------------------------------------------------------------------------------

||| A thread-safe mutable variable.
|||
||| This comes with several atomic operations: `readMVar`,
||| `writeMVar`, `modifyMVar`, and `evalState`.
|||
||| "Atomic" in this context means, that during such an operation,
||| no other thread will be able to access the mutable variable.
|||
||| This uses a `System.Concurrency.Mutex` internally, so it will only
||| be available on the Scheme backends.
export
record MVar a where
  constructor MV
  ref  : IORef a
  lock : Mutex

export
newMVar : a -> IO (MVar a)
newMVar v = [| MV (newIORef v) makeMutex |]

withLock : MVar a -> (IORef a -> IO b) -> IO b
withLock mv f = do
  mutexAcquire mv.lock
  vb <- f mv.ref
  mutexRelease mv.lock
  pure vb

export %inline
readMVar : MVar a -> IO a
readMVar mv = withLock mv readIORef

export %inline
writeMVar : MVar a -> a -> IO ()
writeMVar mv v = withLock mv (`writeIORef` v)

export %inline
modifyMVar : MVar a -> (a -> a) -> IO ()
modifyMVar mv f = withLock mv (`modifyIORef` f)

export
evalState : MVar a -> (a -> (a,b)) -> IO b
evalState mv f =
  withLock mv $ \ref => do
    (st,res) <- f <$> readIORef ref
    writeIORef ref st
    pure res

export
evalIO : MVar a -> (a -> (a,IO b)) -> IO b
evalIO mv f =
  withLock mv $ \ref => do
    (st,res) <- f <$> readIORef ref
    writeIORef ref st
    res

--------------------------------------------------------------------------------
-- Deferred
--------------------------------------------------------------------------------

||| A deferred value is initially empty and can be set exactly once.
export
record Deferred a where
  constructor D
  var  : MVar (Maybe a)
  cond : Condition

export
fromMVar : MVar (Maybe a) -> IO (Deferred a)
fromMVar mv = D mv <$> makeCondition

export
newDeferred : IO (Deferred a)
newDeferred = [| D (newMVar Nothing) makeCondition |]

covering
get' : (acq : Bool) -> Deferred a -> IO a
get' b d = do
  when b (mutexAcquire d.var.lock)
  v <- readIORef d.var.ref
  case v of
    Just x  => mutexRelease d.var.lock $> x
    Nothing => conditionWait d.cond d.var.lock >> get' False d

||| Blocks the current thread while waiting on the deferred
||| value to be filled with a result.
export covering %inline
get : Deferred a -> IO a
get = get' True

export %inline
clearGet : Deferred a -> IO (Maybe a)
clearGet d = do
  Just v <- readMVar d.var | Nothing => pure Nothing
  writeMVar d.var Nothing
  pure $ Just v

export %inline
tryGet : Deferred a -> IO (Maybe a)
tryGet = readMVar . var

export
complete : Deferred a -> a -> IO Bool
complete d v = do
  b <- evalState d.var $ \case
         Just x  => (Just x, False)
         Nothing => (Just v, True)
  conditionBroadcast d.cond
  pure b

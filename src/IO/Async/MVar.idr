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
tryGet : Deferred a -> IO (Maybe a)
tryGet d = readMVar d.var

export
complete : Deferred a -> a -> IO Bool
complete d v = do
  b <- evalState d.var $ \case
         Just x  => (Just x, False)
         Nothing => (Just v, True)
  conditionBroadcast d.cond
  pure b

--------------------------------------------------------------------------------
-- MQueue
--------------------------------------------------------------------------------

||| A thread-safe work queue.
export
record MQueue a where
  [noHints]
  constructor MQ
  queue : MVar (Queue a)
  cond  : Condition

export
newMQueue : IO (MQueue a)
newMQueue = [| MQ (newMVar empty) makeCondition |]

export
enqueue : MQueue a -> a -> IO ()
enqueue q v = modifyMVar q.queue (`enqueue` v) >> conditionSignal q.cond

export
enqueueAll : MQueue a -> List a -> IO ()
enqueueAll q [] = pure ()
enqueueAll q vs = modifyMVar q.queue (`enqueueAll` vs) >> conditionSignal q.cond

covering
dequeue' : Bool -> MQueue a -> IO a
dequeue' b q = do
  when b (mutexAcquire q.queue.lock)
  q1 <- readIORef q.queue.ref
  case dequeue q1 of
    Nothing => do
      conditionWait q.cond q.queue.lock
      dequeue' False q
    Just (v,q2) => do
      writeIORef q.queue.ref q2
      mutexRelease q.queue.lock
      pure v

export covering %inline
dequeue : MQueue a -> IO a
dequeue = dequeue' True

--------------------------------------------------------------------------------
-- Worker
--------------------------------------------------------------------------------
--
-- export
-- record WorkST a where
--   constructor W
--   stopped : IORef Bool
--   queue   : MQueue a
--   act     : (a -> IO ()) -> a -> IO ()
--
-- export
-- newWorkST : ((a -> IO ()) -> a -> IO ()) -> IO (WorkST a)
-- newWorkST fun = [| W (newIORef False) newMQueue (pure fun) |]
--
-- namespace WorkST
--   export
--   stop : WorkST a -> IO ()
--   stop w = do
--     mutexAcquire w.queue.queue.lock
--     writeIORef w.stopped True
--     conditionBroadcast w.queue.cond
--     mutexRelease w.queue.queue.lock
--
--   export %inline
--   submit : a -> WorkST a -> IO ()
--   submit v w = enqueue w.queue v
--
--   export %inline
--   submitAll : List a -> WorkST a -> IO ()
--   submitAll vs w = enqueueAll w.queue vs
--
--   covering
--   process' : Bool -> WorkST a -> IO ()
--   process' b w = do
--     when b (mutexAcquire w.queue.queue.lock)
--     q1    <- readIORef w.queue.queue.ref
--     case dequeue q1 of
--       Nothing => do
--         False <- readIORef w.stopped
--           | True => mutexRelease w.queue.queue.lock
--         conditionWait w.queue.cond w.queue.queue.lock
--         process' False w
--
--       Just (v,q2) => do
--         writeIORef w.queue.queue.ref q2
--         mutexRelease w.queue.queue.lock
--         w.act (`submit` w) v
--         process' True w
--
--   export covering %inline
--   process : WorkST a -> IO ()
--   process = process' True
--
-- export
-- record WorkPool a where
--   constructor WP
--   st : WorkST a
--   ts : List ThreadID
--
-- export covering
-- newWorkPool : (n : Nat) -> ((a -> IO ()) -> a -> IO ()) -> IO (WorkPool a)
-- newWorkPool n fun = do
--   w  <- newWorkST fun
--   ts <- traverse (\x => fork $ process w) [1..n]
--   pure $ WP w ts
--
-- namespace WorkPool
--   export
--   stop : WorkPool a -> IO ()
--   stop (WP st ts) = stop st >> traverse_ (\x => threadWait x >> putStrLn "Thread done") ts
--
--   export %inline
--   submit : a -> WorkPool a -> IO ()
--   submit v = submit v . st
--
--   export %inline
--   submitAll : List a -> WorkPool a -> IO ()
--   submitAll vs = submitAll vs . st

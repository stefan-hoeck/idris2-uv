module IO.Async.Fiber

import Data.IORef
import Data.SortedMap
import System.Concurrency
import IO.Async.Outcome
import IO.Async.Token

%default total

--------------------------------------------------------------------------------
-- Execution Context
--------------------------------------------------------------------------------

public export
record ExecutionContext where
  [noHints]
  constructor EC
  tokenGen : TokenGen
  wakeup   : IO ()
  submit   : IO () -> IO ()
  limit    : Nat

export %inline %hint
ecToTokenGen : ExecutionContext => TokenGen
ecToTokenGen @{ec} = ec.tokenGen

export %inline
submitAndWakeup : ExecutionContext -> IO () -> IO ()
submitAndWakeup ec io = ec.submit io >> ec.wakeup

--------------------------------------------------------------------------------
-- Fibers
--------------------------------------------------------------------------------

public export
data AnyFiber : Type

export
record Fiber (es : List Type) (a : Type) where
  constructor MkFiber
  ec        : ExecutionContext
  mutex     : Mutex
  parent    : Maybe AnyFiber
  token     : Token
  children  : IORef (SortedMap Token AnyFiber)
  canceled  : IORef Bool
  outcome   : IORef (Maybe $ Outcome es a)

data AnyFiber : Type where
  AF : Fiber es a -> AnyFiber

withLock : Mutex -> IO a -> IO a
withLock m f = do
  mutexAcquire m
  res <- f
  mutexRelease m
  pure res

export %inline
poll : HasIO io => Fiber es a -> io (Maybe $ Outcome es a)
poll fbr = liftIO $ withLock fbr.mutex (readIORef fbr.outcome)

export
cancelIO : Fiber es a -> IO ()
cancelIO fbr =
  withLock fbr.mutex (writeIORef fbr.canceled True) >>
  fbr.ec.wakeup

export %inline
cancelAny : AnyFiber -> IO ()
cancelAny (AF f) = cancelIO f

removeChild : AnyFiber -> Token -> IO ()
removeChild (AF fbr) k =
  withLock fbr.mutex (modifyIORef fbr.children $ delete k)

addChild : AnyFiber -> Token -> AnyFiber -> IO ()
addChild (AF fbr) k v =
  withLock fbr.mutex (modifyIORef fbr.children $ insert k v)

export
clearChildren : AnyFiber -> IO (List AnyFiber)
clearChildren (AF f) =
  withLock f.mutex $ do
    cs <- readIORef f.children
    writeIORef f.children empty
    pure $ values cs

export
commit : Fiber es a -> Outcome es a -> IO ()
commit fbr o = do
  run <- withLock fbr.mutex $ do
    readIORef fbr.outcome >>= \case
      Just _  => pure (pure ())
      Nothing => do
        writeIORef fbr.outcome (Just o)
        pure $
          for_ fbr.parent (`removeChild `fbr.token) >>
          fbr.ec.wakeup
  run

export %inline
canceled : AnyFiber -> IO Bool
canceled (AF fbr) = withLock fbr.mutex (readIORef fbr.canceled)

export
newFiber : ExecutionContext -> (parent : Maybe AnyFiber) -> IO (Fiber es a)
newFiber ec p = do
  fib <- [| MkFiber
              (pure ec)
              makeMutex
              (pure p)
              token
              (newIORef empty)
              (newIORef False)
              (newIORef Nothing)
         |]
  for_ p $ \x => addChild x fib.token (AF fib)
  pure fib

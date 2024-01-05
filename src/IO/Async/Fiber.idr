module IO.Async.Fiber

import Data.SortedMap
import IO.Async.CancelState
import IO.Async.Outcome
import IO.Async.MVar
import IO.Async.Token

%default total

public export
record Fiber (es : List Type) (a : Type) where
  constructor MkFiber
  parent   : Maybe (MVar CancelState)
  token    : Token
  canceled : MVar CancelState
  outcome  : Deferred (Outcome es a)

export
newFiber : TokenGen => (parent : Maybe (MVar CancelState)) -> IO (Fiber es a)
newFiber parent = do
  c <- newMVar (CS empty False 0)
  t <- token
  for_ parent $ \p => addChild p t c
  o <- newDeferred
  pure $ MkFiber parent t c o

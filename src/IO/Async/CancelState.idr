module IO.Async.CancelState

import Data.Nat
import Data.SortedMap
import IO.Async.MVar
import IO.Async.Token

%default total

public export
record CancelState where
  constructor CS
  children     : SortedMap Token (MVar CancelState)
  canceled     : Bool

export
cancel : MVar CancelState -> IO ()
cancel v =
  evalIO v $ \cs =>
    let cs2 := {canceled := True, children := empty} cs
     in (cs2, assert_total $ traverse_ cancel cs.children)

export %inline
removeChild : MVar CancelState -> Token -> IO ()
removeChild v t = modifyMVar v {children $= delete t}

export
addChild : MVar CancelState -> Token -> MVar CancelState -> IO ()
addChild v t c =
  evalIO v $ \cs =>
    if cs.canceled
       then (cs, ignore $ cancel c)
       else ({children $= insert t c} cs, pure ())

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
  uncancelable : Nat

export
stopped : CancelState -> Bool
stopped (CS _ True 0) = True
stopped _             = False

cancelVar : MVar CancelState -> (CancelState -> CancelState) -> IO CancelState
cancelVar mv f = evalState mv $ \x => let x2 := f x in (x2,x2)

export
cancel : MVar CancelState -> IO CancelState
cancel v =
  evalIO v $ \cs =>
    let cs2 := {canceled := True, children := empty} cs
        act := assert_total $ traverse_ cancel cs.children
     in (cs2, act $> cs2)

export %inline
inc : MVar CancelState -> IO ()
inc v = modifyMVar v {uncancelable $= S}

export %inline
dec : MVar CancelState -> IO ()
dec v = modifyMVar v {uncancelable $= pred}

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

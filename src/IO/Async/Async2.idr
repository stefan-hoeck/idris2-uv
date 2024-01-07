module IO.Async.Async2

import Control.WellFounded
import Data.Nat
import IO.Async.Fiber
import IO.Async.MVar
import IO.Async.Outcome

%default total

public export
data Cancelable = U | C

export
disp : Cancelable -> String
disp C = "cancelable"
disp U = "uncancelable"

export
data Async : Cancelable -> List Type -> Type -> Type

data Prim : List Type -> Type -> Type where
  Sync   : IO (Outcome es a) -> Prim es a
  CB     : ((Outcome es (Maybe a) -> IO ()) -> IO ()) -> Prim es a
  Start  : Async c es a -> Prim es (Fiber es a)
  Poll   : Deferred (Outcome es a) -> Prim es a
  Cancel : Prim es ()

export
data Async : Cancelable -> List Type -> Type -> Type where
  AP   : {c : _} -> Prim es a -> Async c es a
  Bind :
       {c : _}
    -> Async c1 es a
    -> (Outcome es a -> Async c2 fs b)
    -> Async c fs b

export
type : Async c es a -> String

primType : Prim es a -> String
primType (Sync x)  = "Sync"
primType (CB f)    = "CB"
primType (Start x) = "Start of \{type x}"
primType (Poll x)  = "Poll"
primType Cancel    = "Cancel"

type (AP {c} x)     = "AP(\{disp c}) of \{primType x}"
type (Bind {c} x f) = "Bind(\{disp c}) of \{type x}"

depth : Async c es a -> Nat
depth (AP x)     = 0
depth (Bind x _) = S $ depth x

module System.Rx.Msg

import Data.DPair
import public Data.List.Quantifiers.Extra

%default total

||| A message being sent along a reactive network
public export
data Msg : (es : List Type) -> (a : Type) -> Type where
  Next  : (vals : List a)  -> Msg es a
  Done  : (vals : List a)  -> Msg es a
  Err   : (err  : HSum es) -> Msg es a

public export
isTerminal : Msg es a -> Bool
isTerminal (Next _) = False
isTerminal _        = True

public export
weaken : Msg [] a -> Msg es a
weaken (Next vs) = Next vs
weaken (Done vs) = Done vs
weaken (Err err) impossible

--------------------------------------------------------------------------------
-- Valid Continuation
--------------------------------------------------------------------------------

||| Proof that message `m2` is a valid continuation of message `m1`.
|||
||| We use this for the most general form of sequentially converting
||| messages to make sure that the information that an upstream source
||| is exhausted (either because it stopped producing values or because
||| it failed with an error) is not being lost sending data downstream.
public export
data ValidContinuation : (m1 : Msg es a) -> (m2 : Msg fs b) -> Type where
  NextToNext : ValidContinuation (Next vs) (Next ws)
  AnyToDone  : ValidContinuation m1 (Done vs)
  AnyToErr   : ValidContinuation m1 (Err x)

||| Valid sequential result of processing a message
public export
0 ValidAfter : Msg es a -> List Type -> Type -> Type
ValidAfter m fs b = Subset (Msg fs b) (ValidContinuation m)

||| Utility for creating a valid `Next` message as a convertion
||| of initial message `m`.
export %inline
vnext : (vs : List a) -> ValidAfter (Next ws) es a
vnext vs = Element (Next vs) NextToNext

||| Utility for creating a valid `Done` message as a convertion
||| of initial message `m`.
export %inline
vdone : (vs : List a) -> ValidAfter m es a
vdone vs = Element (Done vs) AnyToDone

||| Utility for creating a valid `Err` message as a convertion
||| of initial message `m`.
export %inline
verr : (x : HSum es) -> ValidAfter m es a
verr x = Element (Err x) AnyToErr

--------------------------------------------------------------------------------
-- Implementations
--------------------------------------------------------------------------------

export
All Show es => Show a => Show (Msg es a) where
  showPrec p (Next vals) = showCon p "Next" $ showArg vals
  showPrec p (Done vals) = showCon p "Done" $ showArg vals
  showPrec p (Err err)   = showCon p "Err" $ showArg err

export
All Eq es => Eq a => Eq (Msg es a) where
  Next x == Next y = x == y
  Done x == Done y = x == y
  Err  x == Err  y = x == y
  _      == _      = False

public export
Functor (Msg es) where
  map f (Next vs) = Next $ map f vs
  map f (Done vs) = Done $ map f vs
  map f (Err e)   = Err e

public export
Foldable (Msg es) where
  foldl f v (Next vs) = foldl f v vs
  foldl f v (Done vs) = foldl f v vs
  foldl f v (Err e)   = v

  foldr f v (Next vs) = foldr f v vs
  foldr f v (Done vs) = foldr f v vs
  foldr f v (Err e)   = v

  foldMap f (Next vs) = foldMap f vs
  foldMap f (Done vs) = foldMap f vs
  foldMap f (Err e)   = neutral

  toList (Next vs) = vs
  toList (Done vs) = vs
  toList (Err e)   = []

  null (Next vs) = null vs
  null (Done vs) = null vs
  null (Err e)   = True

public export
Traversable (Msg es) where
  traverse f (Next vals) = Next <$> traverse f vals
  traverse f (Done vals) = Done <$> traverse f vals
  traverse f (Err err)   = pure (Err err)

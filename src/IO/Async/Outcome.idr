module IO.Async.Outcome

import public Data.List.Quantifiers.Extra

%default total

public export
0 Result : List Type -> Type -> Type
Result es a = Either (HSum es) a

public export
data Outcome : List Type -> Type -> Type where
  Succeeded : (res : a) -> Outcome es a
  Error     : (err : HSum es) -> Outcome es a
  Canceled  : Outcome es a

export
toOutcome : Result es a -> Outcome es a
toOutcome (Right v)   = Succeeded v
toOutcome (Left errs) = Error errs

module IO.Async.Resource

import Data.List.Quantifiers.Extra
import IO.Async.Async

%default total

public export
interface Resource a where
  release : a -> Async [] ()

export
useMany :
     {auto rs : All Resource ts}
  -> All (Async es) ts
  -> (HList ts -> Async es a)
  -> Async es a
useMany           []        f = f []
useMany @{_ :: _} (v :: vs) f = do
  rv <- v
  finally (useMany vs $ f . (rv::)) (release rv)

export
use1 :
     {auto rs : Resource v}
  -> Async es v
  -> (v -> Async es a)
  -> Async es a
use1 x f = do
  rv <- x
  finally (f rv) (release rv)

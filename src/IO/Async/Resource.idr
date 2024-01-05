module IO.Async.Resource

import Data.List.Quantifiers.Extra
import IO.Async.Async

%default total

public export
interface Resource a where
  release : HasIO io => a -> io ()

export
use :
     {auto rs : All Resource ts}
  -> All (Async es) ts
  -> (HList ts -> Async es a)
  -> Async es a
use []                  f = f []
use @{_ :: _} (v :: vs) f = do
  rv <- v
  finally (use vs $ f . (rv::)) (release rv)

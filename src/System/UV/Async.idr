module System.UV.Async

import public System.UV.Error

%default total

public export
record Async (es : List Type) (a : Type) where
  constructor AS
  async : (Outcome es a -> IO ()) -> IO ()

export %inline
outcome : Outcome es a -> Async es a
outcome v = AS $ \cb => cb v

%inline
pure' : a -> Async e a
pure' = outcome . Right

export %inline
delay : Lazy a -> Async es a
delay v = AS $ \cb => cb (Right v)

export %inline
fail : HSum es -> Async es a
fail = outcome . Left

export %inline
throw : Has e es => e -> Async es a
throw = fail . inject

export %inline
bindOutcome : Async es a -> (Outcome es a -> Async fs b) -> Async fs b
bindOutcome (AS aa) f = AS $ \g => aa $ \o => (f o).async g

export
onOutcome : Async es a -> (Outcome es a -> Async [] ()) -> Async es a
onOutcome (AS aa) f = AS $ \g => aa $ \o => (f o).async (\_ => g o)

export
onErr : Async es a -> (HSum es -> Async [] ()) -> Async es a
onErr as f = onOutcome as (either f (const $ pure' ()))

export %inline
onErr' : Async es a -> Async [] () -> Async es a
onErr' as = onErr as . const

export %inline
finally : Async es a -> Async [] () -> Async es a
finally aa = onOutcome aa . const

%inline
bind : Async es a -> (a -> Async es b) -> Async es b
bind aa f = bindOutcome aa (either fail f)

export %inline
Functor (Async es) where
  map f v = bind v (pure' . f)

export
Applicative (Async es) where
  pure = pure'
  af <*> aa = bind af (<$> aa)

export %inline
Monad (Async es) where
  (>>=) = bind

export %inline
sync : IO (Outcome es a) -> Async es a
sync io = AS (io >>=)

export %inline
HasIO (Async es) where
  liftIO = sync . map Right

export %inline
run : Async [] () -> IO ()
run (AS f) = f (\_ => pure ())

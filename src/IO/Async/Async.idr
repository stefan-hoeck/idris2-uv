module IO.Async.Async

import IO.Async.Fiber
import IO.Async.MVar
import IO.Async.Outcome
import IO.Async.Token

%default total

--------------------------------------------------------------------------------
-- Cancelability
--------------------------------------------------------------------------------

-- Marks a section of an asynchronous computation to be
-- cancelable (`C`), uncancelable (`U`), or taking its cancelability
-- from the parent scope `P` (which is typically the default)
data Cancelability = U | P | C

%inline
Semigroup Cancelability where
  p <+> P = p
  _ <+> p = p

%inline
Monoid Cancelability where
  neutral = P

disp : Cancelability -> String
disp C = "cancelable"
disp P = "parent"
disp U = "uncancelable"

--------------------------------------------------------------------------------
-- Async data type
--------------------------------------------------------------------------------

||| An asynchronous, cancelable computation with automatic
||| resource management.
|||
||| An asynchronous computation that runs to completion either
||| terminates with an error of one of the error types in list `es`,
||| a result of type `a`
|||
||| Note: The cancelability of a computation can be either set to
||| "cancelable" (the computation will no longer be run if the fiber
||| it is running on has been canceled), "uncancelable" (the computation
||| will be run to completion, even if the fiber it is running on
||| has been canceled), or "parent" (the default), where the cancelability
||| is taken from the outer scope with the outermost scope being
||| "cancelable".
export
data Async : List Type -> Type -> Type where
  Term   : Outcome es a -> Async es a

  Cancel : Async es a

  Self   : Async es AnyFiber

  Ctxt   : Async es ExecutionContext

  Sync   : Cancelability -> IO (Result es a) -> Async es a

  PollC  : IO (Maybe $ Outcome es a) -> Async [] () -> Async es a

  Poll   : IO (Maybe $ Outcome es a) -> Async es a

  Start  : Cancelability -> Async es a -> Async es (Fiber es a)

  -- generalized monadic bind
  Bind   :
       Cancelability
    -> Async es a
    -> (Outcome es a -> Async fs b)
    -> Async fs b

--------------------------------------------------------------------------------
-- Interface Implementations
--------------------------------------------------------------------------------

export %inline
succeed : a -> Async es a
succeed = Term . Succeeded

export %inline
sync : IO (Result es a) -> Async es a
sync = Sync P

bind : Async es a -> (a -> Async es b) -> Async es b
bind x f =
  Bind P x $ \case
    Succeeded v => f v
    Error x     => Term (Error x)
    Canceled    => Term Canceled

export
Functor (Async es) where
  map f aa = bind aa (succeed . f)

export %inline
Applicative (Async es) where
  pure      = succeed
  af <*> aa = bind af (<$> aa)

export %inline
Monad (Async es) where
  (>>=) = bind

export
HasIO (Async es) where
  liftIO = sync . map Right

--------------------------------------------------------------------------------
-- MonadCancel
--------------------------------------------------------------------------------

export
uncancelable : Async fs a -> Async fs a
uncancelable (Sync x y)   = Sync U y
uncancelable (Bind x y f) = Bind U y f
uncancelable v            = v

export
cancelable : Async fs a -> Async fs a
cancelable (Sync P y)   = Sync C y
cancelable (Bind P y f) = Bind C y f
cancelable v            = v

export
strictCancelable : Async fs a -> Async fs a
strictCancelable (Sync _ y)   = Sync C y
strictCancelable (Bind _ y f) = Bind C y f
strictCancelable v            = v

export
canceled : Async es ()
canceled = Cancel

export
join : Fiber es a -> Async fs (Outcome es a)
join f = PollC (map Succeeded <$> poll f) (liftIO $ cancelIO f)

export
cancel : Fiber es a -> Async fs ()
cancel f =
  uncancelable $ do
    liftIO (cancelIO f)
    ignore $ Poll (map Succeeded <$> poll f)

export
cancelAny : AnyFiber -> Async [] ()
cancelAny (AF f) = cancel f

||| Runs an asynchronous computation in the background on a new fiber.
|||
||| The resulting fiber can be canceled from the current fiber, and
||| we can semantically block the current fiber to whait for the background
||| computation to complete.
|||
||| See also `(.cancel)` and `(.await)`.
export %inline
start : Async es a -> Async es (Fiber es a)
start as = Start P as

--------------------------------------------------------------------------------
-- MonadError
--------------------------------------------------------------------------------

export %inline
fail : HSum es -> Async es a
fail = Term . Error

export %inline
throw : Has e es => e -> Async es a
throw = fail . inject

export %inline
handleErrors : (HSum es -> Async fs a) -> Async es a -> Async fs a
handleErrors f x =
  Bind U x $ \case
    Succeeded x => Term $ Succeeded x
    Error x     => f x
    Canceled    => Term Canceled

export %inline
dropErrs : Async es () -> Async [] ()
dropErrs = handleErrors (const $ pure ())

export %inline
handle : All (\x => x -> Async [] a) es -> Async es a -> Async [] a
handle hs = handleErrors (collapse' . hzipWith id hs)

export
guaranteeCase : Async es a -> (Outcome es a -> Async [] ()) -> Async es a
guaranteeCase as f =
  Bind U as $ \o => Bind U (uncancelable $ f o) (\_ => Term o)

export %inline
onCancel : Async es a -> Async [] () -> Async es a
onCancel as x = guaranteeCase as $ \case Canceled => x; _ => pure ()

||| Guarantees to run the given cleanup hook in case a fiber
||| has been canceled or failed with an error.
|||
||| See `guarantee` for additional information.
export
onAbort : Async es a -> (cleanup : Async [] ()) -> Async es a
onAbort as h =
  guaranteeCase as $ \case
    Canceled => h
    Error _  => h
    _        => pure ()

||| Guarantees to run the given cleanup hook in case
||| the given computation finishes with an outcome.
|||
||| See `guarantee` for additional information.
export %inline
finally : Async es a -> (cleanup : Async [] ()) -> Async es a
finally aa v = guaranteeCase aa (\_ => v)

export %inline
forget : Async es a -> Async [] ()
forget as = Bind P as (\_ => pure ())

export
consume : Async es a -> (Outcome es a -> IO ()) -> Async [] ()
consume as cb = forget $ guaranteeCase as (liftIO . cb)

export
bracketCase :
     Async es a
  -> (a -> Async es b)
  -> ((a,Outcome es b) -> Async [] ())
  -> Async es b
bracketCase acquire use release =
  uncancelable $ do
    res <- acquire
    guaranteeCase (use res) (\o => release (res,o))

export %inline
bracket : Async es a -> (a -> Async es b) -> (a -> Async [] ()) -> Async es b
bracket acquire use release =
  bracketCase acquire use (release . fst)

--------------------------------------------------------------------------------
-- Async
--------------------------------------------------------------------------------

export %inline
executionContext : Async es ExecutionContext
executionContext = Ctxt

export
cancelableAsync :
     ((Outcome es a -> IO ()) -> IO (Maybe $ Async [] ()))
  -> Async es a
cancelableAsync reg =
  uncancelable $ do
    ec <- executionContext
    as <- cancelable $ liftIO $ do
      m <- newMVar Nothing
      c <- reg (\o => modifyMVar m (<|> Just o) >> ec.wakeup)
      pure $ maybe (Poll $ readMVar m) (PollC $ readMVar m) c
    as

||| Registers a callback (of type `Outcome es a -> IO ()`) at some
||| external resource and finishes once the callback has been invoked
||| with an outcome.
|||
||| This will semantically block the current fiber.
|||
||| If you want to run this in the background without blocking,
||| wrap it with `start`.
export %inline
async : ((Outcome es a -> IO ()) -> IO ()) -> Async es a
async reg = cancelableAsync (\o => reg o $> Nothing)

||| Semantically blocks the current fiber until one
||| of the given fibers has produced an outcome, in which
||| the others are canceled immediately.
|||
||| This is useful if you for instance have several abort conditions
||| such as a timer and a signal from the operating system, and want
||| to stop your process as soon as the first of the conditions
||| occurs.
export
raceF : List (Async es (Fiber es a)) -> Async es a
raceF fs = do
  bracket
    (sequence fs)
    (\fibers => PollC (liftIO $ pollAll fibers) (traverse_ cancel fibers))
    (\fibers => traverse_ cancel fibers)
  where
    pollAll : List (Fiber es a) -> IO (Maybe $ Outcome es a)
    pollAll []        = pure Nothing
    pollAll (x :: xs) = do
      Nothing <- poll x | v => pure v
      pollAll xs

||| Alias for `raceF . traverse start`.
export %inline
race : (xs : List $ Async es a) -> Async es a
race = raceF . map start

injections : All f ts -> All (\t => (v : t) -> HSum ts) ts
injections []        = []
injections (x :: xs) = Here :: mapProperty (There .) (injections xs)

||| Runs a heterogeneous list of asynchronous computations in parallel,
||| keeping only the one that finishes first.
export %inline
raceAny : All (Async es) ts -> Async es (HSum ts)
raceAny xs = race . forget $ hzipWith map (injections xs) xs

collectOutcomes : All (Outcome es) ts -> Outcome es (HList ts)
collectOutcomes []                 = Succeeded []
collectOutcomes (Succeeded r :: t) = (r::) <$> collectOutcomes t
collectOutcomes (Error x     :: t) = Error x
collectOutcomes (Canceled    :: t) =
  case collectOutcomes t of
    Error x => Error x
    _       => Canceled

||| Accumulates the results of the given heterogeneous list of
||| fibers in a heterogeneous list.
export
parF : All (Async es . Fiber es) ts -> Async es (HList ts)
parF fs = do
  fibers <- hsequence fs
  PollC (pollAll fibers) (ignore . hsequence $ mapProperty cancel fibers)
  where
    pollAll : All (Fiber es) ss -> IO (Maybe $ Outcome es (HList ss))
    pollAll =
        map (map collectOutcomes . hsequence)
      . hsequence
      . mapProperty poll

||| Runs the given computations in parallel and collects the outcomes
||| in a heterogeneous list.
export %inline
par : All (Async es) ts -> Async es (HList ts)
par = parF . mapProperty start

--------------------------------------------------------------------------------
-- Unique (cats-effects interface, follows from HasIO)
--------------------------------------------------------------------------------

export %inline
unique : (tg : TokenGen) => Async es Token
unique = token

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

data Stack : (es : List Type) -> (a : Type) -> Type where
  Nil  : Stack [] ()
  (::) :
       (Cancelability, (Outcome es a -> Async fs b))
    -> Stack fs b
    -> Stack es a

set : Cancelability -> Async es a -> Async es a
set x (Sync y z)   = Sync (x <+> y) z
set x (Bind y z f) = Bind (x <+> y) z f
set _ y            = y

observeCancelation : Cancelability -> AnyFiber -> IO Bool
observeCancelation U _ = pure False
observeCancelation _ f = canceled f

covering
step :
     {auto ec : ExecutionContext}
  -> Nat
  -> AnyFiber
  -> Async es a
  -> Stack es a
  -> IO ()
step 0 m act stck = submitAndWakeup ec (step ec.limit m act stck)

step (S k) m (Bind c x f) stck = step k m (set c x) ((c,f)::stck)

step (S k) m (Term o) []         =
  clearChildren m >>= \case
    [] => pure ()
    cs => step k m (traverse_ cancelAny cs) []

step (S k) m (Term o) ((c,f)::t) = do
  False <- observeCancelation c m | True => step k m (Term Canceled) t
  step k m (set c $ f o) t

step (S k) m (Sync c act) stck = do
  False <- observeCancelation c m | True => step k m (Term Canceled) stck
  r <- act
  step k m (Term $ toOutcome r) stck

step (S k) m (PollC io cncl) stck = do
  False  <- canceled m
    | True => step k m (uncancelable cncl) ((U, \_ => Poll io) :: stck)
  Just o <- io | Nothing => ec.submit (step k m (PollC io cncl) stck)
  step k m (Term o) stck

step (S k) m (Poll io) stck = do
  Just o <- io | Nothing => ec.submit (step k m (Poll io) stck)
  step k m (Term o) stck

step (S k) m Self stck = step k m (pure m) stck

step (S k) m Ctxt stck = step k m (pure ec) stck

step (S k) m Cancel stck = cancelAny m >> step k m (Term Canceled) stck

step (S k) m (Start c as) stck = do
  False <- observeCancelation c m | True => step k m (Term Canceled) stck
  fib   <- newFiber ec (Just m)
  submitAndWakeup ec $ step ec.limit (AF fib) (consume as $ commit fib) []
  step k m (pure fib) stck

parameters {auto ec : ExecutionContext}

  export covering
  runAsync : Async [] () -> IO ()
  runAsync as = do
    fib <- newFiber {a = ()} {es = []} ec Nothing
    submitAndWakeup ec $ step ec.limit (AF fib) as []

  export covering %inline
  runAsyncWith : Async es a -> (Outcome es a -> IO ()) -> IO ()
  runAsyncWith as cb = runAsync $ consume as cb

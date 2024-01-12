module IO.Async.Async

import Data.IORef

import IO.Async.CancelState
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

cancelNow : Bool -> Cancelability -> Bool
cancelNow True C = True
cancelNow _    _ = False

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
data Async : (es : List Type) -> (a : Type) -> Type

-- Primitive computations
data Prim : List Type -> Type -> Type where
  -- lifte `IO` action
  Sync   : IO (Outcome es a) -> Prim es a

  -- registering function for a callback that running forever
  CB     : ((Outcome es (Maybe a) -> IO ()) -> IO ()) -> Prim es a

  -- spawn a new fiber with the given computation
  Start  : Async es a -> Prim es (Fiber es a)

  -- repeatedly poll the given `IO` action until int yields a `Just`
  Poll   : IO (Maybe $ Outcome es a) -> Prim es a

  -- cancel the current fiber
  Cancel : Prim es ()

export
data Async : List Type -> Type -> Type where
  -- a primitive computation together with its cancelability
  AP   : Cancelability -> Prim es a -> Async es a

  -- generalized monadic bind plus its cancelability.
  --
  -- Note: Even if the cancelability is set to "cancelable" (`C`),
  -- one of the child computations might still be uncancelable
  -- and must be run to completion.
  AB : Cancelability -> Async es a -> (Outcome es a -> Async fs b) -> Async fs b

||| Print some debugging information about the inner
||| structure and cancelability of an `Async` computation.
export
type : Async es a -> String

primType : Prim es a -> String
primType (Sync x)  = "Sync"
primType (CB f)    = "CB"
primType (Start x) = "Start of \{type x}"
primType (Poll x)  = "Poll"
primType Cancel    = "Cancel"

type (AP c x)   = "AP(\{disp c}) of \{primType x}"
type (AB c x f) = "AB(\{disp c}) of \{type x}"

depth : Async es a -> Nat
depth (AP _ _)   = 0
depth (AB _ x _) = S $ depth x

--------------------------------------------------------------------------------
-- Synchronous utilities
--------------------------------------------------------------------------------

||| Lifts a synchronous `IO` action into the `Async` monad.
export %inline
sync : IO (Outcome es a) -> Async es a
sync io = AP P $ Sync io

||| Lifts a synchronous `IO` action with the possibility of failure
||| into the `Async` monad.
export %inline
liftEither : IO (Result es a) -> Async es a
liftEither = sync . map toOutcome

||| Lifts a pure value into the `Async` monad.
export %inline
liftResult : Result es a -> Async es a
liftResult = liftEither . pure

||| Lifts a pure value into the `Async` monad.
export %inline
succeed : a -> Async es a
succeed = liftResult . Right

%inline
canceled : Async es a
canceled = sync . pure $ Canceled

||| Fail with an error.
export %inline
fail : HSum es -> Async es a
fail = liftResult . Left

||| Fail with a specific error.
export %inline
throw : Has e es => e -> Async es a
throw = fail . inject

--------------------------------------------------------------------------------
-- Cancelling fibers
--------------------------------------------------------------------------------

||| Sets the given computation's cancelability to "cancelable".
export
cancelable : Async es a -> Async es a
cancelable (AP _ x)   = AP C x
cancelable (AB _ x f) = AB C x f

||| Sets the given computation's cancelability to "uncancelable".
export
uncancelable : Async es a -> Async es a
uncancelable (AP _ x)   = AP U x
uncancelable (AB _ x f) = AB U x f

||| Cancels the current fiber, stopping all asynchronous computations
||| as soon as possible by respecting their cancelability.
export %inline
cancel : Async es ()
cancel = AP P Cancel

--------------------------------------------------------------------------------
-- Interface Implementations
--------------------------------------------------------------------------------

-- implementation of (>>=)
bind : Async es a -> (a -> Async es b) -> Async es b
bind aa f =
  AB P aa $ \case
    Succeeded v => f v
    Error err   => fail err
    Canceled    => canceled

export
Functor (Async es) where
  map f aa = bind aa (succeed . f)

export
Applicative (Async es) where
  pure      = succeed
  af <*> aa = bind af (<$> aa)

export
Monad (Async es) where
  (>>=) = bind

export
HasIO (Async es) where
  liftIO = sync . map Succeeded

--------------------------------------------------------------------------------
-- Error handling
--------------------------------------------------------------------------------

export
catch : (HSum es -> Async fs a) -> Async es a -> Async fs a
catch f as =
  AB U as $ \case
    Succeeded a => pure a
    Error err   => f err
    Canceled    => canceled

export
dropErrs : Async es () -> Async [] ()
dropErrs = catch (const $ pure ())

export
handle : All (\x => x -> Async [] a) es -> Async es a -> Async [] a
handle hs = catch (collapse' . hzipWith id hs)

--------------------------------------------------------------------------------
-- Resource management
--------------------------------------------------------------------------------

||| Run the given cleanup function after `act` returns a result no matter
||| what.
|||
||| This is the core utility for doing resource management: After you
||| aqcuire a scarce resource such as a file handle that needs to be
||| released once a computation is done, wrap it in one of the
||| finalizers such as `guarantee`, `onCancel`, `onArbort`, or
||| `finally`.
export
guarantee :
     (act : Async es a)
  -> (cleanup : Outcome es a -> Async [] ())
  -> Async es a
guarantee as fun =
  AB U as (\o => AB U (fun o) (\_ => sync $ pure o))

||| Guarantees to run the given cleanup hook in case a fiber
||| has been canceled.
|||
||| See `guarantee` for additional information.
export
onCancel : Async es a -> (cleanup : Async [] ()) -> Async es a
onCancel as h =
  guarantee as $ \case
    Canceled => h
    _        => pure ()

||| Guarantees to run the given cleanup hook in case a fiber
||| has been canceled or failed with an error.
|||
||| See `guarantee` for additional information.
export
onAbort : Async es a -> (cleanup : Async [] ()) -> Async es a
onAbort as h =
  guarantee as $ \case
    Canceled => h
    Error _  => h
    _        => pure ()

||| Guarantees to run the given cleanup hook in case
||| the given computation finishes with an outcome.
|||
||| See `guarantee` for additional information.
export %inline
finally : Async es a -> (cleanup : Async [] ()) -> Async es a
finally aa v = guarantee aa (\_ => v)

--------------------------------------------------------------------------------
-- Asynchronous utilities
--------------------------------------------------------------------------------

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
async reg = AP P $ CB $ \x => reg (x . map Just)

||| Asynchronously evaluates a pure computation.
export %inline
delay : Lazy a -> Async es a
delay v = async $ \cb => cb (Succeeded v)

||| Like `async`, but the callback might be invoked many times with
||| a result of `Nothing`, indicating that although the computation
||| has been run, it is not finished yet.
|||
||| An example for this could be a timer that repeatedly invokes its callback
||| after a given duration.
|||
||| This will semantically block the current fiber.
|||
||| If you want to run this in the background without blocking,
||| wrap it with `start`.
export %inline
forever : ((Outcome es (Maybe a) -> IO ()) -> IO ()) -> Async es a
forever f = AP P $ CB f

||| Repeatedly invokes the given `IO` action until it returns
||| a `Just`.
|||
||| This will semantically block the current fiber.
|||
||| If you want to run this in the background without blocking,
||| wrap it with `start`.
export %inline
poll : IO (Maybe $ Outcome es a) -> Async es a
poll = AP P . Poll

||| Runs an asynchronous computation in the background on a new fiber.
|||
||| The resulting fiber can be canceled from the current fiber, and
||| we can semantically block the current fiber to whait for the background
||| computation to complete.
|||
||| See also `(.cancel)` and `(.await)`.
export %inline
start : Async es a -> Async es (Fiber es a)
start as = AP P $ Start as

||| Cancels a computation on another fibers.
|||
||| This will semantically block the current fiber until
||| the cancellee has finished with an outcome.
export
(.cancel) : Fiber es a -> Async es ()
(.cancel) f = do
  liftIO $
    for_ f.parent (\p => removeChild p f.token) >>
    ignore (cancel f.canceled)
  AB P (poll $ tryGet f.outcome) (\_ => succeed ())

||| Semantically blocks the current fiber until the target fiber
||| has produced a result, in which case we continue with that
||| result.
export
(.await) : Fiber es a -> Async es a
(.await) f = poll $ tryGet f.outcome

||| Semantically blocks the current fiber until one
||| of the two given fibers has produced an outcome, in which
||| case the second fiber is canceled immediately.
|||
||| This is useful if you for instance have several abort conditions
||| such as a timer and a signal from the operating system, and want
||| to stop your process as soon as the first of the two conditions
||| occurs.
export
raceF : (x,y : Async es (Fiber es a)) -> Async es a
raceF x y = do
  fx <- x
  fy <- y
  finally
    (cancelable $ poll $
       tryGet fx.outcome >>= \case
         Nothing => tryGet fy.outcome
         Just v  => pure (Just v)
    ) (dropErrs $ fx.cancel >> fy.cancel)

||| Alias for `raceF (start x) (start y)`.
export %inline
race : (x,y : Async es a) -> Async es a
race x y = raceF (start x) (start y)

||| Alias for `race (map Left x) (map Right y)`
export %inline
raceEither : (x : Async es a) -> (y : Async es b) -> Async es (Either a b)
raceEither x y = race (map Left x) (map Right y)

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

data View : List Type -> Type -> Type where
  VP : Cancelability -> Prim es a -> View es a
  VB :
       Cancelability
    -> Prim es a
    -> Cancelability
    -> (Outcome es a -> Async fs b)
    -> View fs b

fromView : View es a -> Async es a
fromView (VP x y)     = AP x y
fromView (VB x y z f) = AB z (AP x y) f

covering
toView : Async es a -> View es a
toView (AP c  y)   = VP c y
toView (AB cp y f) =
  case y of
    AP cc p   => VB (cp <+> cc) p cp f
    AB cc z g => toView $ AB (cp <+> cc) z (\x => AB cp (g x) f)

||| Intermediary state of a running asynchronous computation
||| concisting of the fiber it is running on and the current
||| state of evaluation.
export
record EvalST where
  constructor EST
  {0 errors : List Type}
  {0 result : Type}
  fiber     : Fiber errors result
  act       : Async errors result

||| Context for running asynchronous computations.
|||
||| It wraps a `TokenGen` for generating unique IDs for
||| freshly spawned fibers, plus a function `submit`,
||| for putting the current evaluation as well as the
||| state of newly started fibers on an evaluation queue.
public export
record AsyncContext where
  [noHints]
  constructor AC
  tokenGen : TokenGen
  submit   : EvalST -> IO ()

export %inline %hint
contextToTokenGen : AsyncContext => TokenGen
contextToTokenGen @{c} = c.tokenGen

-- result of a single step of evaluation.
-- boolean values indicate whether the current fiber has
-- been canceled before or during the evaluation.
data EvalRes : (es : List Type) -> Type -> Type where
  Cede : Bool -> Async es a -> EvalRes es a
  Done : Bool -> Outcome es a -> EvalRes es a

-- debug string for outcomes
doneType : Outcome es a -> String
doneType (Succeeded res) = "Succeeded"
doneType (Error err) = "Error"
doneType Canceled = "Canceled"

-- debug string for outcomes
resDebugMsg : EvalRes es a -> String
resDebugMsg (Cede b x) = "Cede (\{show b}) of type \{type x} and depth \{show $ depth x}"
resDebugMsg (Done b x) = "Done (\{show b}) of type \{doneType x}"

set : Cancelability -> Async es a -> Async es a
set x (AP y z)   = AP (x <+> y) z
set x (AB y z f) = AB (x <+> y) z f

parameters {auto ctxt : AsyncContext}

  prim :
       MVar CancelState
    -> Bool
    -> Cancelability
    -> Prim es a
    -> IO (EvalRes es a)
  prim m True C _ = pure (Done True Canceled)

  prim m b c (Sync x) = Done b <$> x

  prim m b c (CB f) = do
    x <- newDeferred
    f $ \case
      Succeeded (Just a) => ignore $ complete x (Succeeded a)
      Succeeded Nothing  => pure ()
      Canceled           => ignore $ complete x Canceled
      Error err          => ignore $ complete x (Error err)
    pure (Cede b . AP c . Poll $ clearGet x)

  prim m b c (Start x) = do
    fbr <- newFiber (Just m)
    ctxt.submit (EST fbr x)
    pure (Done b $ Succeeded fbr)

  prim m b c (Poll x)  = do
    Nothing <- x | Just v => pure (Done b v)
    pure (Cede b . AP c $ Poll x)

  prim m b c Cancel = pure (Done True Canceled)

  covering
  step :
       MVar CancelState
    -> Bool
    -> View es a
    -> PrimIO (EvalRes es a)
  step m b (VP c p)     w = toPrim (prim m b c p) w
  step m b (VB c p x f) w =
    let MkIORes o w2 := toPrim (prim m b c p) w
     in case o of
          Done b2 z => case cancelNow b2 x of
            True  => MkIORes (Done True Canceled) w2
            False => step m b2 (toView . set x $ f z) w2
          Cede b2 z => MkIORes (Cede b2 $ AB x z f) w2

  export covering
  eval : EvalST -> IO ()
  eval (EST f act) = do
    cs  <- readMVar f.canceled
    res <- primIO (step f.canceled cs.canceled (toView $ set C act))
    case res of
      Cede b act' => cancel b f >> ctxt.submit (EST f act')
      Done b res  => cancel b f >> ignore (complete f.outcome res)

--------------------------------------------------------------------------------
-- Running asynchronous computations
--------------------------------------------------------------------------------

||| Runs the given asynchronous computation to completion
||| invoking the given callback once it is done.
export covering
onAsync : AsyncContext => Async es a -> (Outcome es a -> IO ()) -> IO ()
onAsync as cb = do
  fb  <- newFiber Nothing
  eval (EST fb $ guarantee as (liftIO . cb))

||| Asynchronously runs the given computation to completion.
export covering %inline
runAsync : AsyncContext => Async [] () -> IO ()
runAsync as = onAsync as (\_ => pure ())

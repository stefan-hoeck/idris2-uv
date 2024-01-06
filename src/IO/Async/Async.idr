module IO.Async.Async

import Data.IORef

import IO.Async.CancelState
import IO.Async.Fiber
import IO.Async.MVar
import IO.Async.Outcome
import IO.Async.Token

%default total

--------------------------------------------------------------------------------
-- Async and core functions
--------------------------------------------------------------------------------

export
data Async : List Type -> Type -> Type where
  Sync         : IO (Outcome es a) -> Async es a
  CB           : ((Outcome es a -> IO ()) -> IO ()) -> Async es a
  Forever      : ((Outcome es (Maybe a) -> IO ()) -> IO ()) -> Async es a
  Bind         : Async es a -> (Outcome es a -> Async fs b) -> Async fs b
  Start        : Async es a -> Async es (Fiber es a)
  Poll         : Deferred (Outcome es a) -> Async es a
  Cancel       : Async es ()
  After        : Async es a -> IO () -> Async es a
  Uncancelable : Async es a -> Async es a
  Cancelable   : Async es a -> Async es a

type : Async es a -> String
type (Sync x) = "Sync"
type (CB f) = "CB"
type (Forever f) = "Forever"
type (Bind x f) = "Bind of \{type x}"
type (Start x) = "Start of \{type x}"
type (Poll x) = "Poll"
type Cancel = "Cancel"
type (After x y) = "After of \{type x}"
type (Uncancelable x) = "Uncancelable of \{type x}"
type (Cancelable x) = "Cancelable of \{type x}"

depth : Async es a -> Nat
depth (Sync x) = 1
depth (CB f) = 1
depth (Forever f) = 1
depth (Bind x f) = S $ depth x
depth (Start x) = S $ depth x
depth (Poll x) = 1
depth Cancel = 1
depth (After x y) = S $ depth x
depth (Uncancelable x) = S $ depth x
depth (Cancelable x) = S $ depth x

public export
0 Canceler : Type
Canceler = {0 es : _} -> {0 a : _} -> Async es a -> Async es a

export %inline
async : ((Outcome es a -> IO ()) -> IO ()) -> Async es a
async = CB

export %inline
forever : ((Outcome es (Maybe a) -> IO ()) -> IO ()) -> Async es a
forever = Forever

export %inline
sync : IO (Outcome es a) -> Async es a
sync = Sync

export %inline
liftEither : IO (Result es a) -> Async es a
liftEither = sync . map toOutcome

export %inline
liftResult : Result es a -> Async es a
liftResult = liftEither . pure

export %inline
succeed : a -> Async es a
succeed = liftResult . Right

%inline
canceled : Async es a
canceled = sync . pure $ Canceled

export %inline
delay : Lazy a -> Async es a
delay v = CB $ \cb => cb (Succeeded v)

export %inline
fail : HSum es -> Async es a
fail = liftResult . Left

export %inline
throw : Has e es => e -> Async es a
throw = fail . inject

bind : Async es a -> (a -> Async es b) -> Async es b
bind aa f =
  Bind aa $ \case
    Succeeded v => f v
    Error err   => fail err
    Canceled    => canceled

export %inline
Functor (Async es) where
  map f aa = bind aa (succeed . f)

export %inline
Applicative (Async es) where
  pure      = succeed
  af <*> aa = bind af (<$> aa)

export %inline
Monad (Async es) where
  (>>=) = bind

export %inline
HasIO (Async es) where
  liftIO = sync . map Succeeded

export %inline
uncancelable : (Canceler -> Async es a) -> Async es a
uncancelable as = Uncancelable $ as Cancelable

export
guarantee : Async es a -> (Outcome es a -> Async [] ()) -> Async es a
guarantee as fun =
  uncancelable $ \f => Bind (f as) (\o => Bind (fun o) (\_ => sync $ pure o))

export
catch : (HSum es -> Async [] a) -> Async es a -> Async [] a
catch f as =
  Bind as $ \case
    Succeeded a => pure a
    Error err   => f err
    Canceled    => canceled

export
handle : All (\x => x -> Async [] a) es -> Async es a -> Async [] a
handle hs = catch (collapse' . hzipWith id hs)

export
onCancel : Async es a -> Async [] () -> Async es a
onCancel as h =
  guarantee as $ \case
    Canceled => h
    _        => pure ()

export
onAbort : Async es a -> Async [] () -> Async es a
onAbort as h =
  guarantee as $ \case
    Canceled => h
    Error _  => h
    _        => pure ()

export %inline
finally : Async es a -> Async [] () -> Async es a
finally aa v = guarantee aa (\_ => v)

export %inline
cancel : Async es ()
cancel = Cancel

export %inline
start : Async es a -> Async es (Fiber es a)
start = Start

export
(.cancel) : Fiber es a -> Async es ()
(.cancel) f = do
  liftIO $
    for_ f.parent (\p => removeChild p f.token) >>
    ignore (cancel f.canceled)
  Bind (Poll f.outcome) (\_ => pure ())

export
(.await) : Fiber es a -> Async es a
(.await) f = Poll f.outcome

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

public export
record EvalST where
  constructor EST
  {0 errors : List Type}
  {0 result : Type}
  fiber : Fiber errors result
  act   : Async errors result

data EvalRes : (es : List Type) -> Type -> Type where
  Cont : Async es a -> EvalRes es a
  Cede : Async es a -> EvalRes es a
  Done : Outcome es a -> EvalRes es a

toRes : CancelState -> EvalRes es ()
toRes cs = Done $ if stopped cs then Canceled else Succeeded ()

doneType : Outcome es a -> String
doneType (Succeeded res) = "Succeeded"
doneType (Error err) = "Error"
doneType Canceled = "Canceled"

resDebugMsg : EvalRes es a -> String
resDebugMsg (Cont x) = "Cont of type \{type x} and depth \{show $ depth x}"
resDebugMsg (Cede x) = "Cede of type \{type x} and depth \{show $ depth x}"
resDebugMsg (Done x) = "Done of type \{doneType x}"

parameters {auto tg : TokenGen}
           (submit  : EvalST -> IO ())

  covering
  step : MVar CancelState -> Async es a -> IO (EvalRes es a)

  covering
  done : MVar CancelState -> Async es a -> IO (EvalRes es a)

  covering
  step' : MVar CancelState -> Async es a -> IO (EvalRes es a)
  step' c act = do
    s <- readMVar c
    if stopped s then done c act else step c act

  export covering
  eval : EvalST -> IO ()
  eval (EST f act) = do
    res <- step' f.canceled act
    -- putStrLn (resDebugMsg res)
    case res of
      Cont act' => submit (EST f act')
      Cede act' => submit (EST f act')
      Done res  => ignore (complete f.outcome res)

  step c (Sync io) = map Done io

  step c (CB f) = do
    var <- newDeferred
    f (ignore . complete var)
    pure (Cede $ Poll var)

  step c (Forever f) = do
    var <- newDeferred
    f $ \case
      Succeeded (Just a) => ignore $ complete var (Succeeded a)
      Succeeded Nothing  => pure ()
      Canceled           => ignore $ complete var Canceled
      Error err          => ignore $ complete var (Error err)
    pure (Cede $ Poll var)

  step c (Bind x f) = do
    step c x >>= \case
      Cont y => step' c (Bind y f)
      Cede y => pure (Cede $ Bind y f)
      Done r => step' c (f r)

  step c (After x y) =
    step c x >>= \case
      Cont v => step' c (After v y)
      Cede v => pure (Cede $ After v y)
      Done o => y $> Done o

  step c (Poll var) = do
    Nothing <- tryGet var | Just v => pure (Done v)
    pure (Cede $ Poll var)

  step c (Start x) = do
    fbr <- newFiber (Just c)
    ignore $ eval (EST fbr x)
    pure (Done $ Succeeded fbr)

  step c (Uncancelable x) = inc c >> step c (After x (dec c))

  step c (Cancelable x) = dec c >> step c (After x (inc c))

  step c Cancel = toRes <$> cancel c

  done c (Bind x f) =
    done c x >>= \case
      Cont v => step' c (Bind v f)
      Cede v => pure (Cede $ Bind v f)
      Done v => step' c (f v)

  done c (After x y) =
    done c x >>= \case
      Cont v => step' c (After v y)
      Cede v => pure (Cede $ After v y)
      Done v => y $> Done v

  done c _ = pure (Done Canceled)

module IO.Async.Async

import Data.IORef

import IO.Async.CancelState
import IO.Async.Fiber
import IO.Async.MVar
import IO.Async.Outcome
import IO.Async.Token

%default total

--------------------------------------------------------------------------------
-- Async data type
--------------------------------------------------------------------------------

data Cancelable = U | P | C

Semigroup Cancelable where
  p <+> P = p
  _ <+> p = p

Monoid Cancelable where
  neutral = P

disp : Cancelable -> String
disp C = "cancelable"
disp P = "parent"
disp U = "uncancelable"

export
data Async : List Type -> Type -> Type

data Prim : List Type -> Type -> Type where
  Sync   : IO (Outcome es a) -> Prim es a
  CB     : ((Outcome es (Maybe a) -> IO ()) -> IO ()) -> Prim es a
  Start  : Async es a -> Prim es (Fiber es a)
  Poll   : IO (Maybe $ Outcome es a) -> Prim es a
  Cancel : Prim es ()

export
data Async : List Type -> Type -> Type where
  AP   : Cancelable -> Prim es a -> Async es a
  Bind :
       Cancelable
    -> Async es a
    -> (Outcome es a -> Async fs b)
    -> Async fs b

export
type : Async es a -> String

primType : Prim es a -> String
primType (Sync x)  = "Sync"
primType (CB f)    = "CB"
primType (Start x) = "Start of \{type x}"
primType (Poll x)  = "Poll"
primType Cancel    = "Cancel"

type (AP c x)     = "AP(\{disp c}) of \{primType x}"
type (Bind c x f) = "Bind(\{disp c}) of \{type x}"

depth : Async es a -> Nat
depth (AP _ _)     = 0
depth (Bind _ x _) = S $ depth x

--------------------------------------------------------------------------------
-- Core functions
--------------------------------------------------------------------------------

export %inline
async : ((Outcome es a -> IO ()) -> IO ()) -> Async es a
async reg = AP P $ CB $ \x => reg (x . map Just)

export %inline
forever : ((Outcome es (Maybe a) -> IO ()) -> IO ()) -> Async es a
forever f = AP P $ CB f

export %inline
sync : IO (Outcome es a) -> Async es a
sync io = AP P $ Sync io

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
delay v = async $ \cb => cb (Succeeded v)

export %inline
fail : HSum es -> Async es a
fail = liftResult . Left

export %inline
throw : Has e es => e -> Async es a
throw = fail . inject

bind : Async es a -> (a -> Async es b) -> Async es b
bind aa f =
  Bind P aa $ \case
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

export
cancelable : Async es a -> Async es a
cancelable (AP _ x)     = AP C x
cancelable (Bind _ x f) = Bind C x f

export
uncancelable : Async es a -> Async es a
uncancelable (AP _ x)     = AP U x
uncancelable (Bind _ x f) = Bind U x f

export %inline
poll : IO (Maybe $ Outcome es a) -> Async es a
poll = AP P . Poll

export
guarantee : Async es a -> (Outcome es a -> Async [] ()) -> Async es a
guarantee as fun =
  Bind U as (\o => Bind U (fun o) (\_ => sync $ pure o))

export
catch : (HSum es -> Async [] a) -> Async es a -> Async [] a
catch f as =
  Bind U as $ \case
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
cancel = AP P Cancel

export %inline
start : Async es a -> Async es (Fiber es a)
start as = AP P $ Start as

export
(.cancel) : Fiber es a -> Async es ()
(.cancel) f = do
  liftIO $
    for_ f.parent (\p => removeChild p f.token) >>
    ignore (cancel f.canceled)
  Bind P (poll $ tryGet f.outcome) (\_ => succeed ())

export
(.await) : Fiber es a -> Async es a
(.await) f = poll $ tryGet f.outcome

export
raceF : Async es (Fiber es a) -> Async es (Fiber es a) -> Async es a
raceF x y = do
  fx <- x
  fy <- y
  v  <- poll $ tryGet fx.outcome >>= \case
          Nothing => tryGet fy.outcome
          Just v  => pure (Just v)
  fx.cancel
  fy.cancel
  pure v

export
race : Async es a -> Async es a -> Async es a

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

public export
record EvalST where
  constructor EST
  {0 errors     : List Type}
  {0 result     : Type}
  fiber         : Fiber errors result
  act           : Async errors result

data EvalRes : (es : List Type) -> Type -> Type where
  Cont : Bool -> Async es a -> EvalRes es a
  Cede : Bool -> Async es a -> EvalRes es a
  Done : Bool -> Outcome es a -> EvalRes es a

toRes : Bool -> EvalRes es ()
toRes b = Done b $ if b then Canceled else Succeeded ()

doneType : Outcome es a -> String
doneType (Succeeded res) = "Succeeded"
doneType (Error err) = "Error"
doneType Canceled = "Canceled"

resDebugMsg : EvalRes es a -> String
resDebugMsg (Cont b x) = "Cont of type \{type x} and depth \{show $ depth x}"
resDebugMsg (Cede b x) = "Cede of type \{type x} and depth \{show $ depth x}"
resDebugMsg (Done b x) = "Done of type \{doneType x}"

set : Cancelable -> Async es a -> Async es a
set x (AP y z)     = AP (x <+> y) z
set x (Bind y z f) = Bind (x <+> y) z f

parameters {auto tg : TokenGen}
           (submit  : EvalST -> IO ())

  prim :
       MVar CancelState
    -> Bool
    -> Cancelable
    -> Prim es a
    -> IO (EvalRes es a)
  prim m b c (Sync x)    = Done b <$> x

  prim m b c (CB f)      = do
    x <- newDeferred
    f $ \case
      Succeeded (Just a) => ignore $ complete x (Succeeded a)
      Succeeded Nothing  => pure ()
      Canceled           => ignore $ complete x Canceled
      Error err          => ignore $ complete x (Error err)
    pure (Cede b . AP c . Poll $ tryGet x)

  prim m b c (Start x) = do
    fbr <- newFiber (Just m)
    submit (EST fbr x)
    pure (Done b $ Succeeded fbr)

  prim m b c (Poll x)  = do
    Nothing <- x | Just v => pure (Done b v)
    pure (Cede b . AP c $ Poll x)

  prim m b c Cancel = pure (Done True Canceled)

  covering
  step :
       MVar CancelState
    -> Bool
    -> Async es a
    -> IO (EvalRes es a)
  step m True (AP C _)     = pure (Done True Canceled)
  step m b    (AP c p)     = prim m b c p
  step m b    (Bind c x f) =
    step m b (set c x) >>= \case
      Cont b2 z => step m b2 (Bind c z f)
      Cede b2 z => pure (Cede b2 $ Bind c z f)
      Done b2 z => step m b2 (set c $ f z)

  export covering
  eval : EvalST -> IO ()
  eval (EST f act) = do
    cs  <- readMVar f.canceled
    res <- step f.canceled cs.canceled (set C act)
    -- putStrLn (resDebugMsg res)
    case res of
      Cont b act' => cancel b f >> submit (EST f act')
      Cede b act' => cancel b f >> submit (EST f act')
      Done b res  => cancel b f >> ignore (complete f.outcome res)

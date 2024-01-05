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
  CB           : ((Outcome es a -> IO ()) -> IO ()) -> Async es a
  Forever      : ((Outcome es (Maybe a) -> IO ()) -> IO ()) -> Async es a
  Bind         : Async es a -> (Outcome es a -> Async fs b) -> Async fs b
  Start        : Async es a -> Async es (Fiber es a)
  Poll         : Deferred (Outcome es a) -> Async es a
  Cancel       : Async es ()
  After        : Async es a -> IO () -> Async es a
  Uncancelable : Async es a -> Async es a
  Cancelable   : Async es a -> Async es a

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
lift : IO (Outcome es a) -> Async es a
lift io = CB (io >>=)

export %inline
liftEither : IO (Result es a) -> Async es a
liftEither res = CB $ \cb => res >>= cb . toOutcome

export %inline
liftResult : Result es a -> Async es a
liftResult res = CB $ \cb => cb (toOutcome res)

export %inline
succeed : a -> Async es a
succeed = liftResult . Right

%inline
canceled : Async es a
canceled = lift . pure $ Canceled

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
  liftIO = lift . map Succeeded

export %inline
uncancelable : (Canceler -> Async es a) -> Async es a
uncancelable as = Uncancelable $ as Cancelable

export
guarantee : Async es a -> (Outcome es a -> Async [] ()) -> Async es a
guarantee as fun =
  uncancelable $ \f => Bind (f as) (\o => Bind (fun o) (\_ => lift $ pure o))

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
(.cancel) : Fiber es a -> Async [] ()
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

toOutcome : CancelState -> Either (Outcome es ()) b
toOutcome cs = Left $ if stopped cs then Canceled else Succeeded ()

public export
record EvalST where
  constructor EST
  {0 errors : List Type}
  {0 result : Type}
  fiber : Fiber errors result
  act   : Async errors result

parameters {auto tg : TokenGen}
           (spawn  : IO (Maybe EvalST -> IO ()))

  covering
  step : MVar CancelState -> Async es a -> IO (Either (Outcome es a) (Async es a))

  covering
  done : MVar CancelState -> Async es a -> IO (Either (Outcome es a) (Async es a))

  covering
  step' :
       MVar CancelState
    -> Async es a
    -> IO (Either (Outcome es a) (Async es a))
  step' c act = do
    s <- readMVar c
    if stopped s then done c act else step c act

  export covering
  eval : (submit : Maybe EvalST -> IO ()) -> EvalST -> IO ()
  eval submit (EST f act) = do
    Left o <- step' f.canceled act | Right act' => submit (Just $ EST f act')
    ignore (complete f.outcome o)
    submit Nothing

  step c (CB f) = do
    var <- newDeferred
    f (ignore . complete var)
    pure (Right $ Poll var)

  step c (Forever f) = do
    var <- newDeferred
    f $ \case
      Succeeded (Just a) => ignore $ complete var (Succeeded a)
      Succeeded Nothing  => pure ()
      Canceled           => ignore $ complete var Canceled
      Error err          => ignore $ complete var (Error err)
    pure (Right $ Poll var)

  step c (Bind x f) = do
    Left o <- step c x | Right as => pure (Right $ Bind as f)
    pure (Right $ f o)

  step c (After x y) = do
    Left o <- step c x | Right as => pure (Right $ After as y)
    y $> Left o

  step c (Poll var) = do
    Nothing <- tryGet var | Just v => pure (Left v)
    pure (Right $ Poll var)

  step c (Start x) = do
    fbr <- newFiber (Just c)
    sub <- spawn
    ignore $ eval sub (EST fbr x)
    pure (Left $ Succeeded fbr)

  step c (Uncancelable x) = inc c $> (Right $ After x (dec c))

  step c (Cancelable x) = dec c $> (Right $ After x (inc c))

  step c Cancel = toOutcome <$> cancel c

  done c (Bind x f) = do
    Left o <- done c x | Right as => pure (Right $ Bind as f)
    pure (Right $ f o)
  done c (After x y) = do
    Left o <- done c x | Right as => pure (Right $ After as y)
    y $> Left o
  done c _ = pure (Left Canceled)

-- fibo : Nat -> Async [] Nat
-- fibo 0 = pure 1
-- fibo 1 = pure 1
-- fibo (S $ S k) = [| fibo k + fibo (S k) |]
--
-- covering
-- counter : Integer -> Async [] ()
-- counter n = do
--   when (n `mod` 1000 == 0) (printLn n)
--   counter (n+1)
--
-- countDown : Nat -> Async [] ()
-- countDown 0     = putStrLn "Done"
-- countDown (S k) =
--   putStrLn "Countdown \{show $ S k}" >> countDown k
--
-- covering
-- main : IO ()
-- main =
--   runAsync $ do
--     for_ [1..1000] $ \x =>
--       ignore $ start (finally (countDown x) (putStrLn "\{show x} canceled"))
--     f1 <- start (fibo 10)
--     f2 <- start (fibo 10)
--     x1 <- f1.await
--     x2 <- f2.await
--     putStrLn "Results ready"
--     finally cancel (printLn (x1 + x2))

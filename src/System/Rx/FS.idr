module System.Rx.FS

import Data.Colist
import Data.IORef
import public Data.List.Quantifiers.Extra

%default total

public export
record Subscription where
  constructor MkSubscription
  request : IO ()
  cancel  : IO ()

export
dummySubscription : Subscription
dummySubscription = MkSubscription (pure ()) (pure ())

public export
data Msg : (es : List Type) -> (a : Type) -> Type where
  Next  : (vals : List a) -> Msg es a
  Done  : (vals : List a) -> Msg es a
  Err   : (err : HSum es) -> Msg es a

public export
record Sink (es : List Type) (a : Type) where
  constructor MkSink
  subscribe : Subscription -> IO ()
  sink      : Msg es a -> IO ()

public export
record Src (es : List Type) (a : Type) where
  constructor MkSrc
  serve : Sink es a -> IO ()

public export
record Pipe (es,fs : List Type) (a,b : Type) where
  constructor MkPipe
  pipe : Src es a -> Src fs b

infixl 1 |>

export %inline
(|>) : Src es a -> Pipe es fs a b -> Src fs b
s1 |> MkPipe pipe = MkSrc $ \snk => pipe s1 `serve` snk

export
syncSrc : s -> (s -> IO (Either (HSum es) (List a, Maybe s))) -> Src es a
syncSrc ini f =
  MkSrc $ \(MkSink subscribe sink) => do
    st <- newIORef (Just ini)

    let request : IO ()
        request = do
          Just s1 <- readIORef st | Nothing => sink (Done [])
          Right (vs,s2) <- f s1
            | Left err => writeIORef st Nothing >> sink (Err err)
          writeIORef st s2
          case s2 of
            Nothing => sink (Done vs)
            Just _  => sink (Next vs)

    subscribe (MkSubscription request (writeIORef st Nothing))

export %inline
safeSrc : s -> (s -> IO (List a, Maybe s)) -> Src [] a
safeSrc s f = syncSrc s (map Right . f)

export %inline
pureSrc : s -> (s -> (List a, Maybe s)) -> Src [] a
pureSrc s f = safeSrc s (pure . f)

export
fromList : List a -> Src [] a
fromList xs = pureSrc xs (, Nothing)

nextStream : SnocList a -> Nat -> Stream a -> (List a, Maybe $ Stream a)
nextStream sx 0 xs          = (sx <>> [], Just $ xs)
nextStream sx (S k) (x::xs) = nextStream (sx :< x) k xs

nextColist : SnocList a -> Nat -> Colist a -> (List a, Maybe $ Colist a)
nextColist sx _ []          = (sx <>> [], Nothing)
nextColist sx 0 xs          = (sx <>> [], Just $ xs)
nextColist sx (S k) (x::xs) = nextColist (sx :< x) k xs

export
fromStream : Nat -> Stream a -> Src [] a
fromStream n xs = pureSrc xs (nextStream [<] n)

export
fromColist : Nat -> Colist a -> Src [] a
fromColist n xs = pureSrc xs (nextColist [<] n)

export
syncPipe :
     (convert : IO (Either (HSum es) (List a) -> IO (Msg fs b)))
  -> Pipe es fs a b
syncPipe convert =
  MkPipe $ \(MkSrc serve) => MkSrc $ \(MkSink subscribe sink) => do
    conv <- convert
    subs <- newIORef dummySubscription

    let request : IO ()
        request = readIORef subs >>= (.request)

        cancel  : IO ()
        cancel = do
          s <- readIORef subs
          writeIORef subs dummySubscription
          s.cancel

        mySink  : Msg es a -> IO ()
        mySink (Done vs) = cancel >> conv (Right vs) >>= sink
        mySink (Next vs) = do
          v <- conv (Right vs)
          case v of
            Next _ => sink v
            _      => cancel >> sink v

        mySink (Err err)   = do
          cancel
          v <- conv (Left err)
          case v of
            Next vs => sink (Done vs)
            _       => cancel >> sink v

    serve (MkSink (writeIORef subs) mySink)
    subscribe (MkSubscription request cancel)

data BufferST : List Type -> Type -> Type where
  Spent   : BufferST es a
  BufErr  : (err : HSum es) -> BufferST es a
  Acc     : (vs : a) -> BufferST es a
  BufDone : (vs : a) -> BufferST es a

req : (ini : s) -> (s -> List b) -> BufferST es s -> (BufferST es s, Maybe $ Msg es b)
req ini f Spent        = (Spent, Nothing)
req ini f (BufErr err) = (Spent, Just $ Err err)
req ini f (Acc vs)     = (Acc ini, Just . Next $ f vs)
req ini f (BufDone vs) = (Spent, Just . Done $ f vs)

export
buffer : s -> (accum : s -> List a -> s) -> (s -> List b) -> Pipe es es a b
buffer ini accum toB =
  MkPipe $ \(MkSrc serve) => MkSrc $ \(MkSink subscribe sink) => do
    subs <- newIORef dummySubscription
    st   <- newIORef (Acc {es} ini)

    let request : IO ()
        request = do
          (v,m) <- req ini toB <$> readIORef st
          writeIORef st v
          traverse_ sink m

        cancel  : IO ()
        cancel = do
          s <- readIORef subs
          writeIORef subs dummySubscription
          writeIORef st Spent
          s.cancel

        mySink  : Msg es a -> IO ()
        -- mySink (Done vs) = cancel >> conv (Right vs) >>= sink
        -- mySink (Next vs) = do
        --   v <- conv (Right vs)
        --   case v of
        --     Next _ => sink v
        --     _      => cancel >> sink v

        -- mySink (Err err)   = do
        --   cancel
        --   v <- conv (Left err)
        --   case v of
        --     Next vs => sink (Done vs)
        --     _       => cancel >> sink v

    serve (MkSink (writeIORef subs) mySink)
    subscribe (MkSubscription request cancel)

export
mappingPipe : (Either (HSum es) (List a) -> Msg fs b) -> Pipe es fs a b
mappingPipe = syncPipe . pure . (pure .)

mealy :
     SnocList b
  -> s
  -> (a -> s -> Maybe (s, Maybe b))
  -> List a -> (Maybe s, List b)
mealy sx st f []        = (Just st, sx <>> [])
mealy sx st f (x :: xs) =
  case f x st of
    Just (st2,vb) => mealy (maybe sx (sx :<) vb) st2 f xs
    Nothing       => (Nothing, sx <>> [])

export
mealyPipe : s -> (a -> s -> Maybe (s, Maybe b)) -> Pipe es es a b
mealyPipe ini f =
  syncPipe $ do
    st <- newIORef (Just ini)

    let fun : Either (HSum es) (List a) -> IO (Msg es b)
        fun (Left x)  = writeIORef st Nothing $> Err x
        fun (Right x) = do
          Just s1 <- readIORef st | Nothing => pure (Done [])
          case mealy [<] s1 f x of
            (Nothing,vs) => writeIORef st Nothing   $> Done vs
            (Just s2,vs) => writeIORef st (Just s2) $> Next vs

    pure fun

export %inline
listPipe : (List a -> List b) -> Pipe es es a b
listPipe f = mappingPipe $ \case Left es => Err es; Right vs => Next (f vs)

export %inline
map : (a -> b) -> Pipe es es a b
map = listPipe . map

export %inline
filter : (a -> Bool) -> Pipe es es a a
filter = listPipe . filter

export %inline
take : Nat -> Pipe es es a a
take n = mealyPipe n (\v => \case 0 => Nothing; S k => Just (k, Just v))

export %inline
drop : Nat -> Pipe es es a a
drop n = mealyPipe n (\v => \case 0 => Just (0, Just v); S k => Just (k, Nothing))

export %inline
delay : Pipe es es a a
delay = mealyPipe Nothing (\v => \case Nothing => Just (Just v, Nothing); Just vold => Just (Just v, Just vold))

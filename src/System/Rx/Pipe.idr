module System.Rx.Pipe

import Data.IORef
import Data.Buffer.Indexed
import Data.ByteString
import System.Rx.Core
import System.Rx.Msg
import System.Rx.Sink
import System.Rx.Source

%default total

errSrc : PipeRef es a -> (HSum es -> IO ()) -> Src [] a
errSrc ref f Nothing  = close ref
errSrc ref f (Just g) = request ref $ \case
  Next vs => g (Next vs)
  Done vs => g (Done vs) >> close ref
  Err  x  => f x >> g (Done []) >> close ref

export
handle : (HSum es -> IO ()) -> Pipe es [] a a
handle f = MkPipe $ do
  ref  <- pipeRef es a (pure ())
  pure (sink ref, errSrc ref f)

export
dropErrs : Pipe es [] a a
dropErrs = handle (const $ pure ())

syncSrc : PipeRef es a -> (List a -> IO (Msg es b)) -> Src es b
syncSrc ref f Nothing  = close ref
syncSrc ref f (Just g) = request ref $ \case
  Next vs => do
    m2 <- f vs
    when (isTerminal m2) (close ref)
    g m2
  Done vs => do
    close ref
    Next vs <- f vs | m => g m
    g (Done vs)
  Err vs => close ref >> g (Err vs)

export
syncPipe : (convert : IO (List a -> IO (Msg es b))) -> Pipe es es a b
syncPipe convert = MkPipe $ do
  conv <- convert
  ref  <- pipeRef es a (pure ())
  pure (sink ref, syncSrc ref conv)

export
mappingPipe : (List a -> Msg es b) -> Pipe es es a b
mappingPipe = syncPipe . pure . (pure .)

mealy :
     SnocList b
  -> s
  -> (a -> s -> Maybe (s, Maybe b))
  -> List a
  -> (Maybe s, List b)
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

    let fun : List a -> IO (Msg es b)
        fun vs = do
          Just s1 <- readIORef st | Nothing => pure (Done [])
          case mealy [<] s1 f vs of
            (Nothing,vs) => writeIORef st Nothing   $> Done vs
            (Just s2,vs) => writeIORef st (Just s2) $> Next vs

    pure fun

export %inline
listPipe : (List a -> List b) -> Pipe es es a b
listPipe f = mappingPipe (Next . f)

export %inline
map : (a -> b) -> Pipe es es a b
map = listPipe . map

export %inline
const : b -> Pipe es es a b
const = map . const

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
zipWithIndex : Pipe es es a (Nat,a)
zipWithIndex = mealyPipe 0 (\v,k => Just (S k, Just (k,v)))

export %inline
show : Show a => Pipe es es a String
show = map show

export %inline
showLines : Show a => Pipe es es a String
showLines = map ((++ "\n") . show)

export %inline
unlines : Pipe es es String String
unlines = map (++ "\n")

export %inline
bytes : Pipe es es String ByteString
bytes = map fromString

--------------------------------------------------------------------------------
-- Buffering
--------------------------------------------------------------------------------
--
-- data BufferST : List Type -> Type -> Type where
--   Empty    : BufferST es s
--   Spent    : BufferST es s
--   Err      : HSum es -> BufferST es s
--   Done     : (val : s) -> BufferST es s
--   Acc      : Nat -> (val : s) -> BufferST es s
--   Overflow : (val : s) -> BufferST es s
--
-- onMsg : Nat -> s -> (s -> a -> s) -> BufferST es s -> Msg es a -> BufferST es s
-- onMsg _ _   f (Acc (S k) v) (Next vs) = Acc k (foldl f v vs)
-- onMsg _ _   f (Acc 0     v) (Next vs) = Overflow (foldl f v vs)
-- onMsg _ _   f (Acc _     v) (Done vs) = Done (foldl f v vs)
--
-- onMsg n ini f Empty         (Next vs) = Acc n (foldl f ini vs)
-- onMsg _ ini f Empty         (Done vs) = Done (foldl f ini vs)
--
-- onMsg _ _   f (Overflow v)  (Done vs) = Done (foldl f v vs)
--
-- onMsg _ _   _ _             (Err v)   = Err v
--
-- onMsg _ _   _ st            _         = st
--
-- afterSending : BufferST es s -> BufferST es s
-- afterSending Empty          = Empty
-- afterSending Spent          = Spent
-- afterSending (Err x)        = Spent
-- afterSending (Done val)     = Spent
-- afterSending (Acc k val)    = Empty
-- afterSending (Overflow val) = Empty
--
-- bufferMsg : (conv : s -> List b) -> BufferST es s -> Msg es b
-- bufferMsg conv (Acc k val)    = Next (conv val)
-- bufferMsg conv Empty          = Next []
-- bufferMsg conv Spent          = Done []
-- bufferMsg conv (Err x)        = Err x
-- bufferMsg conv (Done val)     = Done (conv val)
-- bufferMsg conv (Overflow val) = Next (conv val)
--
-- record BufferRefs (es : List Type) (s,a,b : Type) where
--   constructor BR
--   snk    : PipeRef es a
--   src    : SourceRef es b
--   buffer : IORef (BufferST es s)
--
-- cancel : BufferRefs es s a b -> IO ()
-- cancel (BR snk src buf) = cancel snk >> writeIORef buf Spent >> drain src
--
-- parameters {0 es    : List Type}
--            (size    : Nat)
--            (ini     : s)
--            (acc     : s -> a -> s)
--            (conv    : s -> List b)
--
--   bufferedSink : BufferRefs es s a b -> Snk es a
--
--   bufferedSrc : BufferRefs es s a b -> Src es b
--
--   bufferedServe : BufferRefs es s a b -> Callback es a
--
--   setBuffer : BufferRefs es s a b -> BufferST es s -> IO ()
--
--   sendBuffer : BufferRefs es s a b -> Callback es b -> BufferST es s -> IO ()
--   sendBuffer br cb st = do
--     writeIORef br.src Waiting
--     cb (bufferMsg conv st)
--     let st2 := afterSending st
--     writeIORef br.buffer st2
--     case st2 of
--       Empty => assert_total $ request br.snk (bufferedServe br)
--       _     => pure ()
--
--   bufferedSrc br Nothing = cancel br
--   bufferedSrc br (Just cb) = do
--     Empty <- readIORef br.buffer | st => sendBuffer br cb st
--     writeIORef br.src (CB cb)
--
--   setBuffer br st = do
--     Nothing <- readIORef br.cb | CB cb => sendBuffer br cb st
--     writeIORef br.buffer st
--     case st of
--       Acc _ _ => assert_total $ request br.snk (bufferedServe br)
--       _       => pure ()
--
--   bufferedSink br snk =
--     sink br.snk snk >> (snk $ Just (bufferedServe br))
--
--   bufferedServe br msg =
--     readIORef br.buffer >>= \st => setBuffer br (onMsg size ini acc st msg)
--
--   export
--   bufferedPipe : Pipe es es a b
--   bufferedPipe = MkPipe $ do
--     snk    <- sinkRef es a
--     cb     <- cbRef es b
--     buffer <- newIORef {a = BufferST es s} Empty
--
--     pure (bufferedSink (BR snk cb buffer), bufferedSrc (BR snk cb buffer))
--
-- ||| Buffers up to `n` chunks of input in a `SnocList`
-- export %inline
-- snocBuffer : Nat -> Pipe es es a a
-- snocBuffer n = bufferedPipe n [<] (:<) (<>> [])
--
-- ||| Buffers up to `n` chunks of input by keeping only the last value
-- export %inline
-- lastBuffer : Nat -> Pipe es es a a
-- lastBuffer n = bufferedPipe n Nothing (const Just) toList
--
-- ||| Buffers only the first chunk of input discarding all later events
-- export %inline
-- firstBuffer : Pipe es es a a
-- firstBuffer = bufferedPipe 0 Nothing (\m,v => m <|> Just v) toList

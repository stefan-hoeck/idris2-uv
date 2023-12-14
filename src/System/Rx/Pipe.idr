module System.Rx.Pipe

import Data.IORef
import Data.Buffer.Indexed
import Data.ByteString
import System.Rx.Core
import System.Rx.Msg
import System.Rx.Sink
import System.Rx.Source

%default total

errSrc : SinkRef es a -> (HSum es -> IO ()) -> Src [] a
errSrc ref f Nothing  = close ref
errSrc ref f (Just g) = request ref $ \case
  Next vs => g (Next vs)
  Done vs => g (Done vs) >> close ref
  Err  x  => f x >> g (Done []) >> close ref

export
handle : (HSum es -> IO ()) -> Pipe es [] a a
handle f = MkPipe $ do
  ref  <- sinkRef es a (pure ())
  pure (sink ref, errSrc ref f)

export
dropErrs : Pipe es [] a a
dropErrs = handle (const $ pure ())

syncSrc : SinkRef es a -> (List a -> IO (Msg es b)) -> Src es b
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
  ref  <- sinkRef es a (pure ())
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
-- Sequencing Sources
--------------------------------------------------------------------------------

data FlatMapST : List Type -> Type -> Type where
  Sources : (cur : Src es b) -> (srcs : List (Source es b)) -> FlatMapST es b
  NoSrc   : FlatMapST es b

parameters (snk : SinkRef es a)           -- upstream facing sink
           (src : SourceRef es b)         -- downstream facing source
           (st  : IORef (FlatMapST es b)) -- currently available sources

  -- cleanup without sending out any more messages to callbacks
  cleanup : IO ()
  cleanup = do
    close snk -- close the sink
    abort src -- signal `Nothing` to the source of sources
    Sources s _ <- readIORef st | NoSrc => pure ()
    s Nothing -- signal `Nothing` to the currently active source

  -- Callback for sending messages downstream
  flatMapB : Callback es b
  flatMapB (Next vs) = emit src vs
  flatMapB (Err x)   = send src (Err x) >> cleanup
  flatMapB (Done vs) = do
    -- our current source is exhausted, so we activate the
    -- next one. In case we have no more sources, we ask
    -- upstream for more, or - if upstream is closed - send
    -- the last bit of data (`vs`) wrapped in a `Done` to
    -- downstream
    Sources _ (h::t) <- readIORef st
      | _ => do
        writeIORef st NoSrc
        b <- closed snk
        if b then send src (Done vs) else emit src vs
    s <- h.mkSource
    writeIORef st (Sources s t)
    emit src vs

  -- Callback for getting sources from upstream.
  covering
  flatMapA : (a -> Source es b) -> Callback es a
  flatMapA f (Next vs) =
    case map f vs of
      -- we got a batch of new sources so we activate the first one
      -- and store the rest for later
      h::t => do
        s <- h.mkSource
        writeIORef st (Sources s t)
        s (Just flatMapB)

      -- we got nothing so we request more sources from upstream
      []   => request snk (flatMapA f)

  flatMapA f (Done vs) = do
    -- like `Next vs` but we can close our sink because upstream
    -- is exhausted
    abort snk
    case map f vs of
      -- we got a last batch of sources so we activate the first one
      -- and store the rest for later
      h::t => do
        s <- h.mkSource
        writeIORef st (Sources s t)
        s (Just flatMapB)
      []   =>
        -- we won't get any more sources from upstream, so we can
        -- signal that we are done to downstream
        writeIORef st NoSrc >> send src (Done [])

  -- upstream responded with an error, so we send that to downstream
  -- and stop everything.
  -- TODO: Should we delay the error and first exhaust the sources we
  --       currently have?
  flatMapA f (Err x) = send src (Err x) >> cleanup

  -- our downstream-facing source
  -- if downstream requests more data (the `Just cb` case), we first
  -- check if there are any active source left. If that's the case,
  -- we ourselves request more data from the active source. Otherwise,
  -- we ask upstream for new sources.
  covering
  flatMapSrc : (a -> Source es b) -> Src es b
  flatMapSrc f Nothing   = cleanup
  flatMapSrc f (Just cb) = do
    True        <- registerCB src cb | False => pure ()
    Sources s _ <- readIORef st      | NoSrc => request snk (flatMapA f)
    s (Just flatMapB)

export covering
flatMap : (a -> Source es b) -> Pipe es es a b
flatMap f = MkPipe $ do
  snk <- sinkRef es a (pure ())
  src <- sourceRef es b (pure ())
  st  <- newIORef (NoSrc {es} {b})
  pure (sink snk, flatMapSrc snk src st f)

--------------------------------------------------------------------------------
-- Buffering
--------------------------------------------------------------------------------

data BufferST : Type -> Type where
  Empty    : BufferST s
  Acc      : Nat -> (val : s) -> BufferST s

record BufferRefs (es : List Type) (s,a,b : Type) where
  constructor BR
  snk    : SinkRef es a
  src    : SourceRef es b
  buffer : IORef (BufferST s)

parameters {0 es    : List Type}
           (size    : Nat)
           (ini     : s)
           (acc     : s -> a -> s)
           (conv    : s -> List b)

  buffer : BufferRefs es s a b -> Msg [] a -> IO Bool
  buffer br msg = do
    False <- hasCB br.src
      | True =>
          case msg of
            Next vs => send br.src (Next $ conv $ foldl acc ini vs) $> True
            Done vs => send br.src (Done $ conv $ foldl acc ini vs) $> True
    readIORef br.buffer >>= \case
      Empty       => writeIORef br.buffer (Acc size $ foldl acc ini msg) $> True
      Acc (S k) v => writeIORef br.buffer (Acc k $ foldl acc v msg) $> True
      Acc 0     v => pure False

  covering
  bufferedSrc : BufferRefs es s a b -> Src es b

  covering
  bufferedCB : BufferRefs es s a b -> Callback es a
  bufferedCB br (Next vs) = do
    True <- buffer br (Next vs) | False => pure ()
    request br.snk (bufferedCB br)
  bufferedCB br (Done vs) = abort br.snk >> ignore (buffer br $ Done vs)
  bufferedCB br (Err x)   = abort br.snk >> send br.src (Err x)

  covering
  sendBuffer : BufferRefs es s a b -> Callback es b -> Nat -> s -> IO ()
  sendBuffer br cb k vs = do
    writeIORef br.buffer Empty
    False <- closed br.snk | _ => abort br.src >> cb (Done $ conv vs)
    when (k == 0) (request br.snk (bufferedCB br))
    cb (Next $ conv vs)

  bufferedSrc br Nothing =
    abort br.src >> close br.snk >> writeIORef br.buffer Empty
  bufferedSrc br (Just cb) = do
    Empty <- readIORef br.buffer | Acc n vs => sendBuffer br cb n vs
    ignore $ registerCB br.src cb

  covering
  bufferedSink : BufferRefs es s a b -> Snk es a
  bufferedSink br src =
    sink br.snk src >> request br.snk (bufferedCB br)

  export covering
  bufferedPipe : Pipe es es a b
  bufferedPipe = MkPipe $ do
    snk    <- sinkRef es a (pure ())
    src    <- sourceRef es b (pure ())
    buffer <- newIORef {a = BufferST s} Empty

    let br := BR snk src buffer
    pure (bufferedSink br, bufferedSrc (BR snk src buffer))

||| Buffers up to `n` chunks of input in a `SnocList`
export covering %inline
snocBuffer : Nat -> Pipe es es a a
snocBuffer n = bufferedPipe n [<] (:<) (<>> [])

||| Buffers up to `n` chunks of input by keeping only the last value
export covering %inline
lastBuffer : Nat -> Pipe es es a a
lastBuffer n = bufferedPipe n Nothing (const Just) toList

||| Buffers only the first chunk of input discarding all later events
export covering %inline
firstBuffer : Pipe es es a a
firstBuffer = bufferedPipe 0 Nothing (\m,v => m <|> Just v) toList

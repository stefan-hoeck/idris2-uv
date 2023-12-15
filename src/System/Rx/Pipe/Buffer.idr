module System.Rx.Pipe.Buffer

import Data.Buffer.Indexed
import Data.ByteString
import Data.IORef
import System.Rx.Core
import System.Rx.Msg
import System.Rx.Sink
import System.Rx.Source

%default total

--------------------------------------------------------------------------------
-- Internals
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

  ||| A buffered pipe keeps requesting data from upstream synchronously
  ||| storing values in a buffer if downstream has not yet requested new
  ||| values.
  |||
  ||| This is useful in combination with "hot" sources, such as streams,
  ||| which keep emitting values no matter whether a callback is currently
  ||| registered or not. The buffered pipe makes sure we keep a backlog
  ||| of emitted values up to a certain point.
  |||
  ||| In case of very slow consumers and very fast produces, it would easily
  ||| be possible to consume an arbitrary amount of memory, thats why we must
  ||| limit the amount of emitted batches of values. After that amount has
  ||| been stored, the buffer overflows, and we start losing data.
  export covering
  bufferedPipe : Pipe es es a b
  bufferedPipe = MkPipe $ do
    snk    <- sinkRef es a (pure ())
    src    <- sourceRef es b (pure ())
    buffer <- newIORef {a = BufferST s} Empty

    let br := BR snk src buffer
    pure (bufferedSink br, bufferedSrc (BR snk src buffer))

--------------------------------------------------------------------------------
-- Common Buffers
--------------------------------------------------------------------------------

||| Buffers up to `n` chunks of input in a `SnocList`
export covering %inline
snocBuffer : Nat -> Pipe es es a a
snocBuffer n = bufferedPipe n [<] (:<) (<>> [])

||| Buffers only the first chunk of input discarding all later batches.
export covering %inline
firstBuffer : Pipe es es a a
firstBuffer = bufferedPipe 0 Nothing (\m,v => m <|> Just v) toList

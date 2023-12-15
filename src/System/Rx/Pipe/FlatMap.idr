module System.Rx.Pipe.FlatMap

import Data.IORef
import System.Rx.Core
import System.Rx.Msg
import System.Rx.Sink
import System.Rx.Source

%default total

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

||| A pipe for converting a "source of sources" by sequentially
||| appending the sources until all of them are exhausted.
|||
||| Note, that the resulting stream will abort upon the first
||| exception encountered, be it from the parent source or one
||| of the child sources. If this is not desired, especially, if
||| the parent source should keep emitting sources even when one
||| of its children fails, make sure to properly handle the child
||| errors.
export covering
flatMap : (a -> Source es b) -> Pipe es es a b
flatMap f = MkPipe $ do
  snk <- sinkRef es a (pure ())
  src <- sourceRef es b (pure ())
  st  <- newIORef (NoSrc {es} {b})
  pure (sink snk, flatMapSrc snk src st f)

module System.Rx.Sink

import Data.IORef
import System.Rx.Msg
import System.Rx.Source
import public Data.Fuel

%default total

||| Alias for a function that registers a callback
||| at a source.
public export
0 Snk : List Type -> Type -> Type
Snk es t = Src es t -> IO ()

||| A sink of values of type `a` able to handle errors of type `HSum es`.
public export
record Sink (es : List Type) (a : Type) where
  constructor MkSink
  mkSink : Fuel -> IO (Snk es a)

public export
data SinkST : List Type -> Type -> Type where
  Init    : IO () -> SinkST es a
  Waiting : IO () -> Callback es a -> SinkST es a
  Active  : IO () -> Src es a -> SinkST es a
  Closed  : SinkST es a
  SnkErr  : HSum es -> SinkST es a

||| Mutable feference where a source is stored.
public export
0 SinkRef : List Type -> Type -> Type
SinkRef es t = IORef (SinkST es t)

||| Creates a new `SinkRef` with handle for releasing resources.
export %inline
sinkRef : (0 es : List Type) -> (0 a : Type) -> IO () -> IO (SinkRef es a)
sinkRef _ _ io = newIORef (Init io)

||| Prepends a resource to be released once a sink closes.
|||
||| If the sink is already closed, the resource is released
||| immediately.
export
prependResource : SinkRef es a -> IO () -> IO ()
prependResource ref io =
  readIORef ref >>= \case
    Init x      => writeIORef ref (Init (io >> x))
    Waiting x f => writeIORef ref (Waiting (io >> x) f)
    Active x f  => writeIORef ref (Active (io >> x) f)
    Closed      => io
    SnkErr x    => io

||| Appends a resource to be released once a sink closes.
|||
||| If the sink is already closed, the resource is released
||| immediately.
export
appendResource :  SinkRef es a -> IO () -> IO ()
appendResource ref io =
  readIORef ref >>= \case
    Init x      => writeIORef ref (Init (x >> io))
    Waiting x f => writeIORef ref (Waiting (x >> io) f)
    Active x f  => writeIORef ref (Active (x >> io) f)
    Closed      => io
    SnkErr x    => io

||| Request a message by registering a callback at a source.
export %inline
request : SinkRef es a -> Callback es a -> IO ()
request ref cb =
  readIORef ref >>= \case
    Init io      => writeIORef ref (Waiting io cb)
    Closed       => cb (Done [])
    Waiting io _ => writeIORef ref (Waiting io cb)
    Active io f  => f (Just cb)
    SnkErr x     => cb (Err x)

export %inline
closed : SinkRef es a -> IO Bool
closed ref =
  readIORef ref >>= \case
    Closed   => pure True
    SnkErr x => pure True
    _        => pure False

||| Close a source, thus initializing its cleanup if necessary.
|||
||| Unlike `close`, this will not send a message to the
||| registered source.
export %inline
abort : SinkRef es a -> IO ()
abort ref = do
  st <- readIORef ref
  writeIORef ref Closed
  case st of
    Active io f  => io
    Init io      => io
    Waiting io f => io
    _            => pure ()

||| Close a source, thus initializing its cleanup if necessary
||| This will send a `Nothing` message to any registered sources.
export %inline
close : SinkRef es a -> IO ()
close ref = do
  st <- readIORef ref
  writeIORef ref Closed
  case st of
    Active io f  => io >> f Nothing
    Init io      => io
    Waiting io f => io >> f (Done [])
    _            => pure ()

||| Closes a sink by sending `Err x` to any waiting callback
||| and setting its state to `SnkErr x`.
export %inline
error : SinkRef es a -> (x : HSum es) -> IO ()
error ref x = do
  st <- readIORef ref
  writeIORef ref (SnkErr x)
  case st of
    Active io f  => io >> f Nothing
    Init io      => io
    Waiting io f => io >> f (Err x)
    _            => pure ()

||| Treats a `SinkRef` as a source: Callbacks will be passed on
||| to the source registered at the sink (if any)
export %inline
source : SinkRef es a -> Src es a
source ref Nothing  = close ref
source ref (Just v) = request ref v

||| Treats a `SinkRef` as a sink by allowing source to be registered
||| in the mutable reference.
export %inline
sink : SinkRef es a -> Snk es a
sink ref srv = do
  readIORef ref >>= \case
    Init io       => writeIORef ref (Active io srv)
    Closed        => srv Nothing
    Waiting io cb => writeIORef ref (Active io srv) >> srv (Just cb)
    Active io f   => writeIORef ref (Active io srv)
    SnkErr _      => srv Nothing

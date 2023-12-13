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
data PipeST : List Type -> Type -> Type where
  Init   : IO () -> PipeST es a
  Reg    : IO () -> Callback es a -> PipeST es a
  Active : IO () -> Src es a -> PipeST es a
  Closed : PipeST es a
  PipErr : HSum es -> PipeST es a

||| Mutable feference where a source is stored.
public export
0 PipeRef : List Type -> Type -> Type
PipeRef es t = IORef (PipeST es t)

||| Creates a new `PipeRef` with handle for releasing resources.
export %inline
pipeRef : (0 es : List Type) -> (0 a : Type) -> IO () -> IO (PipeRef es a)
pipeRef _ _ io = newIORef (Init io)

||| Prepends a resource to be released once a pipe closes.
|||
||| If the pipe is already closed, the resource is released
||| immediately.
export
prependResource : PipeRef es a -> IO () -> IO ()
prependResource ref io =
  readIORef ref >>= \case
    Init x     => writeIORef ref (Init (io >> x))
    Reg x f    => writeIORef ref (Reg (io >> x) f)
    Active x f => writeIORef ref (Active (io >> x) f)
    Closed     => io
    PipErr x   => io

||| Appends a resource to be released once a pipe closes.
|||
||| If the pipe is already closed, the resource is released
||| immediately.
export
appendResource :  PipeRef es a -> IO () -> IO ()
appendResource ref io =
  readIORef ref >>= \case
    Init x     => writeIORef ref (Init (x >> io))
    Reg x f    => writeIORef ref (Reg (x >> io) f)
    Active x f => writeIORef ref (Active (x >> io) f)
    Closed     => io
    PipErr x   => io

||| Request a message by registering a callback at a source.
export %inline
request : PipeRef es a -> Callback es a -> IO ()
request ref cb =
  readIORef ref >>= \case
    Init io     => writeIORef ref (Reg io cb)
    Closed      => cb (Done [])
    Reg io _    => writeIORef ref (Reg io cb)
    Active io f => f (Just cb)
    PipErr x    => cb (Err x)

||| Close a source, thus initializing its cleanup if necessary
export %inline
close : PipeRef es a -> IO ()
close ref = do
  st <- readIORef ref
  writeIORef ref Closed
  case st of
    Active io f => io >> f Nothing
    Init io     => io
    Reg io f    => io >> f (Done [])
    _           => pure ()

||| Closes a pipe by sending `Err x` to any waiting callback
||| and setting its state to `PipErr x`.
export %inline
error : PipeRef es a -> (x : HSum es) -> IO ()
error ref x = do
  st <- readIORef ref
  writeIORef ref (PipErr x)
  case st of
    Active io f => io >> f Nothing
    Init io     => io
    Reg io f    => io >> f (Err x)
    _           => pure ()

||| Treats a `PipeRef` as a source: Callbacks will be passed on
||| to the source registered at the sink (if any)
export %inline
source : PipeRef es a -> Src es a
source ref Nothing  = close ref
source ref (Just v) = request ref v

||| Treats a `PipeRef` as a sink by allowing source to be registered
||| in the mutable reference.
export %inline
sink : PipeRef es a -> Snk es a
sink ref srv = do
  readIORef ref >>= \case
    Init io     => writeIORef ref (Active io srv)
    Closed      => srv Nothing
    Reg io cb   => writeIORef ref (Active io srv) >> srv (Just cb)
    Active io f => writeIORef ref (Active io srv)
    PipErr _    => srv Nothing

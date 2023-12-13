module System.Rx.Source

import Data.IORef
import System.Rx.Msg

%default total

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

||| A callback that can be invoked with a message.
public export
0 Callback : List Type -> Type -> Type
Callback es t = Msg es t -> IO ()

||| Alias for a function where we can register callbacks.
|||
||| Registering `Nothing` should be interpreted as "canceling the source".
public export
0 Src : List Type -> Type -> Type
Src es t = Maybe (Callback es t) -> IO ()

||| A source of values of type `a` with the potential of failing
||| with errors of type `es`.
public export
record Source (es : List Type) (a : Type) where
  constructor MkSource
  mkSource : IO (Src es a)

export %inline
pureSrc : Src es a -> Source es a
pureSrc = MkSource . pure

--------------------------------------------------------------------------------
-- Stateless Sources
--------------------------------------------------------------------------------

||| The empty source that will synchronously respond with `Done []`
export %inline
empty' : Src es a
empty' = traverse_ ($ Done [])

||| A source that never responds
export %inline
never' : Src es a
never' _ =  pure ()

||| A source that always responds with an error
export
fail' : Has e es => e -> Src es a
fail' err = traverse_ ($ Err (inject err))

||| A source that always responds with an error.
|||
||| This is an alias for `fail'` that can help with type inference.
export %inline
fail1' : e -> Src [e] a
fail1' = fail'

||| The empty source that will synchronously respond with `Done []`
export
empty : Source es a
empty = pureSrc empty'

||| A source that never responds
export
never : Source es a
never = pureSrc never'

||| A source that always responds with an error
export
fail : Has e es => e -> Source es a
fail err = pureSrc $ fail' err

||| A source that always responds with an error.
|||
||| This is an alias for `fail` that can help with type inference.
export %inline
fail1 : e -> Source [e] a
fail1 err = pureSrc $ fail1' err

||| Sends the given list of values in a single `Done` message to its
||| callbacks.
export %inline
batch : List a -> Source es a
batch vs = pureSrc $ traverse_ ($ Done vs)

||| Sends the given value in a single `Done` message to its callbacks.
export %inline
once : a -> Source es a
once = batch . pure

--------------------------------------------------------------------------------
-- Stateful Sources
--------------------------------------------------------------------------------

||| State of a stateful, non-buffered source.
public export
data SourceST : List Type -> Type -> Type where
  ||| The source is waiting for a callback to be registered.
  ||| The `IO` action is a cleanup hook for when the source is closed.
  Waiting : IO () -> SourceST es a

  ||| A callback has been registered awaiting the next message.
  ||| The `IO` action is a cleanup hook for when the source is closed.
  CB      : IO () -> Callback es a -> SourceST es a

  ||| The source has been closed and its resources released.
  ||| It will send `Done []` immediately to any callback that
  ||| still registers.
  Closed  : SourceST es a

  ||| The source encountered an error.
  ||| Its resources have been released and it will immediately
  ||| send `Err err` to any callback that still registers.
  SrcErr  : HSum es -> SourceST es a

export
onMsg : Msg es a -> SourceST es a -> (IO (), SourceST es a)
onMsg (Next vs) (CB y f)    = (f (Next vs), Waiting y)
onMsg (Done vs) (CB y f)    = (f (Done vs) >> y, Closed)
onMsg (Err e)   (CB y f)    = (f (Err e)   >> y, SrcErr e)
onMsg (Done vs) (Waiting y) = (y, Closed)
onMsg (Err e)   (Waiting y) = (y, SrcErr e)
onMsg _         st          = (pure (), st)

||| Alias for mutable reference that stores a callback.
public export
0 SourceRef : List Type -> Type -> Type
SourceRef es t = IORef (SourceST es t)

||| Creates a mutable reference for handling stateful sources.
export %inline
sourceRef : (0 es : List Type) -> (0 a : Type) -> IO () -> IO (SourceRef es a)
sourceRef _ _ io = newIORef (Waiting io)

||| Send a message to a registered callback (if any).
|||
||| The callback will be removed afterwards. It will have to register
||| itself again if it wants to receive more messages.
|||
||| In case the message is `Done _` or `Err _`, the resource will be
||| changed to the appropriate state and all resources cleaned up.
export %inline
send : SourceRef es a -> Msg es a -> IO ()
send ref m = do
  st <- readIORef ref
  let (io,st2) := onMsg m st
  writeIORef ref st2
  io

||| Emits a chunk of values from a source.
|||
||| If no callback is registered or the source is closed or stuck
||| with an error, no action is taken. Otherwise, the registered
||| callback is invoked and the source's state set to "waiting".
export %inline
emit : SourceRef es a -> List a -> IO ()
emit ref vs = send ref (Next vs)

||| Like `emit` but emits a single value.
export %inline
emit1 : SourceRef es a -> a -> IO ()
emit1 ref = emit ref . pure

||| Closes a source by sending `Done []` to any registered callback
||| and setting its state to `Closed`.
export %inline
close : SourceRef es a -> IO ()
close ref = send ref (Done [])

||| Closes a source by sending `Err x` to any registered callback
||| and setting its state to `SrcErr x`.
export %inline
error : Has e es => SourceRef es a -> (x : e) -> IO ()
error ref x = send ref (Err $ inject x)

export
registerCB : SourceRef es a -> Callback es a -> IO ()
registerCB ref cb = do
  readIORef ref >>= \case
    Waiting io => writeIORef ref (CB io cb)
    Closed     => cb (Done [])
    CB io f    => writeIORef ref (CB io cb)
    SrcErr x   => cb (Err x)

||| Convert a mutable reference for callbacks plus a cleanup action
||| to a "hot" source.
|||
||| A "hot source" is a source that emits messages no matter whether
||| a callback is registered or not, such as a timer.
export
hotSrc : SourceRef es a -> Src es a
hotSrc ref Nothing  = close ref
hotSrc ref (Just f) = registerCB ref f

||| A cold source is one that emits only after a callback has
||| been registered.
|||
||| After one message, it lies dormant until another callback is
||| registered and, thus, another message is requested.
export
coldSrc : SourceRef es a -> (Callback es a -> IO ()) -> Src es a
coldSrc ref _     Nothing  = close ref
coldSrc ref serve (Just f) = do
  registerCB ref f
  CB _ _ <- readIORef ref | _ => pure ()
  serve (send ref)

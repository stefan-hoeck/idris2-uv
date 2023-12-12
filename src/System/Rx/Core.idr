module System.Rx.Core

import Data.IORef
import public Data.List.Quantifiers.Extra

%default total

--------------------------------------------------------------------------------
-- Messages
--------------------------------------------------------------------------------

public export
data Msg : (es : List Type) -> (a : Type) -> Type where
  Next  : (vals : List a) -> Msg es a
  Done  : (vals : List a) -> Msg es a
  Err   : (err  : HSum es) -> Msg es a

export
isTerminal : Msg es a -> Bool
isTerminal (Next _) = False
isTerminal _        = True

--------------------------------------------------------------------------------
-- Callbacks
--------------------------------------------------------------------------------

emptyHandle : a -> IO ()
emptyHandle = \_ => pure ()

||| A callback that can be invoked with a message.
public export
0 Callback : List Type -> Type -> Type
Callback es t = Msg es t -> IO ()

||| Alias for mutable reference that stores a callback.
public export
0 CBRef : List Type -> Type -> Type
CBRef es t = IORef (Maybe $ Callback es t)

||| Creates a new reference for storing a callback.
export %inline
cbRef : (0 es : List Type) -> (0 a : Type) -> IO (CBRef es a)
cbRef _ _ = newIORef Nothing

||| Send a message to a callback.
export %inline
send : CBRef es a -> Msg es a -> IO ()
send cr m = do
  Just cb <- readIORef cr | Nothing => pure ()
  writeIORef cr Nothing
  cb m

export %inline
clearCB : CBRef es a -> IO ()
clearCB ref = writeIORef ref Nothing

export %inline
registerCB : CBRef es a -> Callback es a -> IO ()
registerCB ref cb = writeIORef ref (Just cb)

--------------------------------------------------------------------------------
-- Sources
--------------------------------------------------------------------------------

||| Alias for a function where we can register callbacks.
|||
||| Registering `Nothing` should be interpreted as "canceling the source".
public export
0 Src : List Type -> Type -> Type
Src es t = Maybe (Callback es t) -> IO ()

||| Reference where a source is stored.
public export
0 SourceRef : List Type -> Type -> Type
SourceRef es t = IORef (Src es t)

||| Creates a new `SourceRef` with a dummy callback handle.
export %inline
sourceRef : (0 es : List Type) -> (0 a : Type) -> IO (SourceRef es a)
sourceRef _ _ = newIORef emptyHandle

||| Request a message by registering a callback at a source.
export %inline
request : SourceRef es a -> Callback es a -> IO ()
request ref g = readIORef ref >>= \f => f (Just g)

||| Cancel a source, thus initializing its cleanup if necessary
export %inline
cancel : SourceRef es a -> IO ()
cancel ref = (readIORef ref >>= ($ Nothing)) >> writeIORef ref emptyHandle

||| Choose between `request` and `cancel` by passing a `Maybe` to a source.
export %inline
source : SourceRef es a -> Maybe (Callback es a) -> IO ()
source ref Nothing  = cancel ref
source ref (Just v) = request ref v

||| A source of values of type `a` with the potential of failing
||| with errors of type `es`.
public export
record Source (es : List Type) (a : Type) where
  constructor MkSource
  mkSource : IO (Src es a)

||| The empty source that will synchronously respond with `Done []`
export
empty : Source es a
empty = MkSource . pure $ traverse_ ($ Done [])

||| A source that never responds
export
never : Source es a
never = MkSource . pure $ const (pure ())

||| A source that always responds with an error
export
fail : Has e es => e -> Src es a
fail err = traverse_ ($ Err (inject err))

||| A source that always responds with an error.
|||
||| This is an alias for `fail` that can help with type inference.
export %inline
fail1 : e -> Src [e] a
fail1 = fail

||| Convert a mutable reference for callbacks plus a cleanup action
||| to a source.
export %inline
toSrc : CBRef es a -> (cleanup : IO ()) -> Src es a
toSrc cb cleanup Nothing  = clearCB cb >> cleanup
toSrc cb cleanup (Just f) = registerCB cb f

--------------------------------------------------------------------------------
-- Sinks
--------------------------------------------------------------------------------

||| Alias for a function that registers a callback
||| at a source.
public export
0 Snk : List Type -> Type -> Type
Snk es t = Src es t -> IO ()

public export
record Sink (es : List Type) (a : Type) where
  constructor MkSink
  mkSink : IO (Snk es a)

public export
0 Pip : (es,fs : List Type) -> (a,b : Type) -> Type
Pip es fs a b = (Snk es a, Src fs b)

public export
record Pipe (es,fs : List Type) (a,b : Type) where
  constructor MkPipe
  mkPipe : IO (Pip es fs a b)

infixl 1 |>, |>>

infixr 1 >-

export %inline
(|>) : Source es a -> Pipe es fs a b -> Source fs b
MkSource s |> MkPipe p = MkSource $ do
  srv        <- s
  (snk, src) <- p
  snk srv
  pure src

export %inline
(|>>) : Source es a -> Sink es a -> IO ()
MkSource mso |>> MkSink msi = do
  srv <- mso
  snk <- msi
  snk srv

export %inline
(>-) : Pipe es fs a b -> Sink fs b -> Sink es a
MkPipe p >- MkSink s = MkSink $ do
  (snk,src) <- p
  f         <- s
  f src
  pure snk

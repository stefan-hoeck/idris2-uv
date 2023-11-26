module System.UV.Resource

import Data.IORef

%default total

||| A resource that can be released. Typical usecases include
||| pointers we want to free or handles we would like to
||| stop.
|||
||| Releasing a resource is an idempotent action: Upon releasing
||| a resource, the release handle will be replaced with a dummy
||| IO action.
export
record Resource where
  constructor MkResource
  ref : IORef (IO ())

||| Register the given IO action as a resource handle.
|||
||| This could be, for instance, a call to `freePtr` or a call
||| to `close` for a uv handle, or a combination of several such
||| actions.
export %inline
handle : HasIO io => IO () -> io Resource
handle = map MkResource . newIORef

||| The neutral IO action that has no effect.
export
unit : IO ()
unit = pure ()

||| Release a managed resource.
|||
||| This is an idempotent action: Releasing the same resource
||| several times has no additional (or negative) effect.
export
release : HasIO io => Resource -> io ()
release (MkResource ref) = do
  act <- readIORef ref
  writeIORef ref unit
  liftIO act

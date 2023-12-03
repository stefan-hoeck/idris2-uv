module System.UV.Signal

import Data.Fuel
import System.UV.Error
import System.UV.Handle
import System.UV.Loop
import System.UV.Pointer
import System.UV.Resource
import public System.UV.Raw.Signal

%default total

start : Fuel -> IO Bool -> Resource -> Ptr Signal -> Bits32 -> UVIO ()

go : Fuel -> IO Bool -> Resource -> Ptr Signal -> Bits32 -> IO ()

start f act res h c = uvio $ uv_signal_start h (go f act res) c

go Dry      act res h c = release res
go (More x) act res h c = do
  True     <- act | False => release res
  Right () <- runEitherT $ start x act res h c | Left _ => release res
  pure ()

parameters {auto l    : UVLoop}
           (reference : Bool)

  ||| Runs the given `IO` action each time the given signal
  ||| is received until it either returns `False` or the `Fuel` runs dry.
  |||
  ||| If `reference` is set to `False`, the signal handle will not be
  ||| referenced at the event loop: The loop will terminate, if there are
  ||| only unreferenced handles left.
  export
  repeatedlyOnSignal : Fuel -> SigCode -> IO Bool -> UVIO Resource
  repeatedlyOnSignal f c act = do
    h <- mallocPtr Signal
    uvio $ uv_signal_init l.loop h
    when (not reference) (uv_unref h)
    res <- manageHandle h
    start f act res h (sigToCode c)
    pure res


  ||| Runs the given `IO` action once when the given signal is received.
  export %inline
  onSignal : SigCode -> IO () -> UVIO Resource
  onSignal c act = repeatedlyOnSignal (limit 1) c (act $> False)

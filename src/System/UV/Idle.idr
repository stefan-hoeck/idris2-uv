module System.UV.Idle

import IO.Async
import IO.Async.Event
import System.UV.Loop
import System.UV.Pointer
import System.UV.Raw.Handle
import System.UV.Raw.Idle

%default total

%inline stopIdle : HasIO io => Ptr Idle -> io ()
stopIdle = ignore . uv_idle_stop

%inline stopCheck : HasIO io => Ptr Check -> io ()
stopCheck = ignore . uv_check_stop

%inline stopPrepare : HasIO io => Ptr Prepare -> io ()
stopPrepare = ignore . uv_prepare_stop

parameters {auto cc : CloseCB}
  export %inline
  Resource (Ptr Idle) where
    release p = stopIdle p >> uv_close p cc

  export %inline
  Resource (Ptr Check) where
    release p = stopCheck p >> uv_close p cc

  export %inline
  Resource (Ptr Prepare) where
    release p = stopPrepare p >> uv_close p cc

parameters {auto l   : UVLoop}
           {auto has : Has UVError es}

  export
  mkIdle : Async es (Ptr Idle)
  mkIdle = mallocPtr Idle >>= uvAct (uv_idle_init l.loop)

  ||| Runs the given `IO` action during the "idle" phase of the event loop.
  export
  onIdle : (Event Nat -> Async es a) -> Async es a
  onIdle run =
    use1 mkIdle $ \pt => do
      ev <- newEvent
      uv $ uv_idle_start pt (\_ => send ev 1 id (+))
      run ev

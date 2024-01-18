module System.UV.Idle

import IO.Async
import System.UV.Loop
import System.UV.Pointer
import System.UV.Raw.Handle
import System.UV.Raw.Idle

%default total

parameters {auto cc : CloseCB}
  export %inline
  Resource (Ptr Idle) where
    release p = uv_close p cc

  export %inline
  Resource (Ptr Check) where
    release p = uv_close p cc

  export %inline
  Resource (Ptr Prepare) where
    release p = uv_close p cc

  idle_stop : HasIO io => Ptr Idle -> io ()
  idle_stop x = ignore (uv_idle_stop x) >> release x

  -- check_stop : Ptr Check -> Async [] ()
  -- check_stop x = ignore (uv_check_stop x) >> release x

  -- prepare_stop : Ptr Prepare -> Async [] ()
  -- prepare_stop x = ignore (uv_prepare_stop x) >> release x

-- parameters {auto l   : UVLoop}
--            {auto has : Has UVError es}

--   export
--   mkIdle : Async es (Ptr Idle)
--   mkIdle = mallocPtr Idle >>= uvAct (uv_idle_init l.loop)
--
--   ||| Runs the given `IO` action during the "idle" phase of the event loop.
--   export
--   onIdle : Async es ()
--   onIdle = do
--     pi <- mkIdle
--     uvOnce' pi (\_ => pure ()) $ \cb =>
--       uv_idle_start pi (\p => idle_stop p >> cb)
--
  -- export
  -- mkCheck : Async es (Ptr Check)
  -- mkCheck = mallocPtr Check >>= uvAct (uv_check_init l.loop)

  -- ||| Runs the given `IO` action during the "check" phase of the event loop.
  -- export
  -- onCheck : Async es (Maybe a) -> Async es a
  -- onCheck as = do
  --   pi <- mkCheck
  --   uvForever' as pi check_stop (uv_check_start pi . const)

  -- export
  -- mkPrepare : Async es (Ptr Prepare)
  -- mkPrepare = mallocPtr Prepare >>= uvAct (uv_prepare_init l.loop)

  -- ||| Runs the given `IO` action during the "prepare" phase of the event loop.
  -- export
  -- onPrepare : Async es (Maybe a) -> Async es a
  -- onPrepare as = do
  --   pi <- mkPrepare
  --   uvForever' as pi prepare_stop (uv_prepare_start pi . const)

module System.UV.Idle

import System.UV.Async
import System.UV.Error
import System.UV.Resource
import System.UV.Loop
import System.UV.Pointer
import System.UV.Raw.Handle
import public System.UV.Raw.Idle

%default total

export
Resource (Ptr Idle) where
  release h = uv_close h freePtr

export
Resource (Ptr Check) where
  release h = uv_close h freePtr

export
Resource (Ptr Prepare) where
  release h = uv_close h freePtr

parameters {auto l   : UVLoop}
           {auto has : Has UVError es}

  export
  mkIdle : Async es (Cancel, Ptr Idle)
  mkIdle = do
    pt <- mallocPtr Idle >>= uvAct (uv_idle_init l.loop)
    c  <- mkCancel (ignore (uv_idle_stop pt) >> release pt)
    pure (c, pt)

  ||| Runs the given `IO` action during the "idle" phase of the event loop.
  export
  onIdle : (Cancel -> Async [] ()) -> Async es Cancel
  onIdle run = do
    (r,pi) <- mkIdle
    uvPar r run $ \cb => uv_idle_start pi (\_ => cb r)

  export
  mkCheck : Async es (Cancel, Ptr Check)
  mkCheck = do
    pt <- mallocPtr Check >>= uvAct (uv_check_init l.loop)
    c  <- mkCancel (ignore (uv_check_stop pt) >> release pt)
    pure (c, pt)

  ||| Runs the given `IO` action during the "check" phase of the event loop.
  export
  onCheck : (Cancel -> Async [] ()) -> Async es Cancel
  onCheck run = do
    (r,pc) <- mkCheck
    uvPar r run $ \cb => uv_check_start pc (\_ => cb r)

  export
  mkPrepare : Async es (Cancel, Ptr Prepare)
  mkPrepare = do
    pt <- mallocPtr Prepare >>= uvAct (uv_prepare_init l.loop)
    c  <- mkCancel (ignore (uv_prepare_stop pt) >> release pt)
    pure (c, pt)

  ||| Runs the given `IO` action during the "prepare" phase of the event loop.
  export
  onPrepare : (Cancel -> Async [] ()) -> Async es Cancel
  onPrepare run = do
    (r,pc) <- mkPrepare
    uvPar r run $ \cb => uv_prepare_start pc (\_ => cb r)

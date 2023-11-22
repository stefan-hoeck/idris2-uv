module System.UV.Handle

import System.FFI
import System.UV.Loop
import System.UV.Util

%default total

export
data UnknownHandle : Type where

export
data Async : Type where

export
data Check : Type where

export
data FsEvent : Type where

export
data FsPoll : Type where

export
data Handle : Type where

export
data Idle : Type where

export
data NamedPipe : Type where

export
data Poll : Type where

export
data Prepare : Type where

export
data Process : Type where

export
data Stream : Type where

export
data Tcp : Type where

export
data Timer : Type where

export
data Tty : Type where

export
data Udp : Type where

export
data Signal : Type where

export
data File : Type where

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_is_active")
prim__uv_is_active : Ptr Handle -> PrimIO Int

%foreign (idris_uv "uv_is_closing")
prim__uv_is_closing : Ptr Handle -> PrimIO Int

%foreign (idris_uv "uv_close")
prim__uv_close : Ptr Handle -> (Ptr Handle -> PrimIO ()) -> PrimIO ()

%foreign (idris_uv "uv_ref")
prim__uv_ref : Ptr Handle -> PrimIO ()

%foreign (idris_uv "uv_unref")
prim__uv_unref : Ptr Handle -> PrimIO ()

%foreign (idris_uv "uv_has_ref")
prim__uv_has_ref : Ptr Handle -> PrimIO Int

%foreign (idris_uv "uv_handle_size")
prim__uv_handle_size : Int -> Int

%foreign (idris_uv "uv_handle_get_data")
prim__uv_handle_get_data : Ptr Handle -> PrimIO AnyPtr

%foreign (idris_uv "uv_handle_set_data")
prim__uv_handle_set_data : Ptr Handle -> AnyPtr -> PrimIO ()

%foreign (idris_uv "uv_handle_type")
prim__uv_handle_type : Ptr Handle -> PrimIO Int

%foreign (idris_uv "uv_handle_type_name")
prim__uv_handle_type_name : Int -> String

%foreign (idris_uv "uv_UNKNOWN_HANDLE")
UV_UNKNOWN_HANDLE : Int

%foreign (idris_uv "uv_ASYNC")
UV_ASYNC : Int

%foreign (idris_uv "uv_CHECK")
UV_CHECK : Int

%foreign (idris_uv "uv_FS_EVENT")
UV_FS_EVENT : Int

%foreign (idris_uv "uv_FS_POLL")
UV_FS_POLL : Int

%foreign (idris_uv "uv_HANDLE")
UV_HANDLE : Int

%foreign (idris_uv "uv_IDLE")
UV_IDLE : Int

%foreign (idris_uv "uv_NAMED_PIPE")
UV_NAMED_PIPE : Int

%foreign (idris_uv "uv_POLL")
UV_POLL : Int

%foreign (idris_uv "uv_PREPARE")
UV_PREPARE : Int

%foreign (idris_uv "uv_PROCESS")
UV_PROCESS : Int

%foreign (idris_uv "uv_STREAM")
UV_STREAM : Int

%foreign (idris_uv "uv_TCP")
UV_TCP : Int

%foreign (idris_uv "uv_TIMER")
UV_TIMER : Int

%foreign (idris_uv "uv_TTY")
UV_TTY : Int

%foreign (idris_uv "uv_UDP")
UV_UDP : Int

%foreign (idris_uv "uv_SIGNAL")
UV_SIGNAL : Int

%foreign (idris_uv "uv_FILE")
UV_FILE : Int

--------------------------------------------------------------------------------
-- Handle
--------------------------------------------------------------------------------

||| libuv handle type used for allocating the required amount of memory
||| for a new handle.
|||
||| Some handles are subtyes of other handles: Their structure is laid out
||| in such a way that they can be used where other the other type is expected.
|||
||| For instance, every libuv handle can be used where a `uv_handle_t`
||| (represented as `Ptr Handle` in Idris) is expected.
public export
data HandleType : Type -> Type where
  UNKNOWN_HANDLE : HandleType UnknownHandle
  ASYNC          : HandleType Async
  CHECK          : HandleType Check
  FS_EVENT       : HandleType FsEvent
  FS_POLL        : HandleType FsPoll
  HANDLE         : HandleType Handle
  IDLE           : HandleType Idle
  NAMEDPIPE      : HandleType NamedPipe
  POLL           : HandleType Poll
  PREPARE        : HandleType Prepare
  PROCESS        : HandleType Process
  STREAM         : HandleType Stream
  TCP            : HandleType Tcp
  TIMER          : HandleType Timer
  TTY            : HandleType Tty
  UDP            : HandleType Udp
  SIGNAL         : HandleType Signal
  FILE           : HandleType File

value : HandleType t -> Int
value UNKNOWN_HANDLE = UV_UNKNOWN_HANDLE
value ASYNC          = UV_ASYNC
value CHECK          = UV_CHECK
value FS_EVENT       = UV_FS_EVENT
value FS_POLL        = UV_FS_POLL
value HANDLE         = UV_HANDLE
value IDLE           = UV_IDLE
value NAMEDPIPE      = UV_NAMED_PIPE
value POLL           = UV_POLL
value PREPARE        = UV_PREPARE
value PROCESS        = UV_PROCESS
value STREAM         = UV_STREAM
value TCP            = UV_TCP
value TIMER          = UV_TIMER
value TTY            = UV_TTY
value UDP            = UV_UDP
value SIGNAL         = UV_SIGNAL
value FILE           = UV_FILE

||| Number of bytes allocated by the given handle type
export %inline
handleSize : HandleType t -> Int
handleSize = prim__uv_handle_size . value

||| Allocate memory for a libuv handle corresponding to the given tag.
export %inline
mallocHandle : HasIO io => HandleType t -> io (Ptr t)
mallocHandle v = prim__castPtr <$> malloc (handleSize v)

||| Free the given libuv handle.
export %inline
freeHandle : HasIO io => Ptr t -> io ()
freeHandle = free . prim__forgetPtr

--------------------------------------------------------------------------------
-- Safe Casts
--------------------------------------------------------------------------------

public export
data HandleCast : Type -> Type -> Type where
  AsyncHandle          : HandleCast Async Handle
  CheckHandle          : HandleCast Check Handle
  Fs_eventHandle       : HandleCast FsEvent Handle
  Fs_pollHandle        : HandleCast FsPoll Handle
  HandleHandle         : HandleCast Handle Handle
  IdleHandle           : HandleCast Idle Handle
  NamedpipeHandle      : HandleCast NamedPipe Handle
  PollHandle           : HandleCast Poll Handle
  PrepareHandle        : HandleCast Prepare Handle
  ProcessHandle        : HandleCast Process Handle
  StreamHandle         : HandleCast Stream Handle
  TcpHandle            : HandleCast Tcp Handle
  TimerHandle          : HandleCast Timer Handle
  TtyHandle            : HandleCast Tty Handle
  UdpHandle            : HandleCast Udp Handle
  SignalHandle         : HandleCast Signal Handle
  FileHandle           : HandleCast File Handle

export
castHandle : {auto 0 prf : HandleCast s t} -> Ptr s -> Ptr t
castHandle = believe_me

--------------------------------------------------------------------------------
-- Safe Casts
--------------------------------------------------------------------------------

parameters {auto has   : HasIO io}
           {auto 0 prf : HandleCast t Handle}

  export %inline
  isActive : Ptr t -> io Bool
  isActive p = intToBool <$> primIO (prim__uv_is_active $ castHandle p)

  export %inline
  isClosing : Ptr t -> io Bool
  isClosing p = intToBool <$> primIO (prim__uv_is_closing $ castHandle p)

  ||| Request a handle to be closed.
  |||
  ||| This *must* be called before releasing the handle from memore,
  ||| which can be done from within the callback or after the callback
  ||| has returned.
  export
  close : Ptr t -> (Ptr Handle -> IO ()) -> io ()
  close p f = primIO $ prim__uv_close (castHandle p) (\h => toPrim $ f h)

  ||| Reference a handle.
  |||
  ||| This is an idempotent action, so calling it several times has no
  ||| additional effect.
  export %inline
  ref : Ptr t -> io ()
  ref p = primIO $ prim__uv_ref (castHandle p)

  ||| Un-reference a handle.
  |||
  ||| This is an idempotent action, so calling it several times has no
  ||| additional effect.
  export %inline
  unref : Ptr t -> io ()
  unref p = primIO $ prim__uv_unref (castHandle p)

  ||| Returns `True` is the handle is currently referenced.
  export %inline
  hasRef : Ptr t -> io Bool
  hasRef p = intToBool <$> primIO (prim__uv_has_ref $ castHandle p)

  ||| Returns a pointer to the data associated with a handle.
  export %inline
  getData : Ptr t -> io AnyPtr
  getData p = primIO $ prim__uv_handle_get_data (castHandle p)

  ||| Sets the data associated with a handle
  export %inline
  setData : Ptr t -> AnyPtr -> io ()
  setData p ap = primIO $ prim__uv_handle_set_data (castHandle p) ap

  ||| Returns the type the current handle.
  export %inline
  handleType : Ptr t -> io Int
  handleType p = primIO $ prim__uv_handle_type (castHandle p)


||| Returns the name of the handle type.
export %inline
handleTypeName : Int -> String
handleTypeName = prim__uv_handle_type_name

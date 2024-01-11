module System.UV.Raw.Callback

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "scheme:lock-object"
prim__lockobject : AnyPtr -> PrimIO ()

%foreign "scheme:unlock-object"
prim__unlockobject : AnyPtr -> PrimIO ()

%foreign "scheme:foreign-callable-code-object"
prim__foreign_callable_code_object : AnyPtr -> AnyPtr

%foreign "scheme:foreign-callable-entry-point"
prim__foreign_callable_entry_point : AnyPtr -> AnyPtr

--------------------------------------------------------------------------------
-- Wrappers
--------------------------------------------------------------------------------

||| A chez scheme code object that can be converted to
||| a foreign callable address.
public export
record CodeObject (a : Type) where
  constructor CO
  ptr : AnyPtr

||| Locks a foreign callable code object, so that it will not be
||| claimed by the Chez garbage collector.
export %inline
lockObject : HasIO io => CodeObject a -> io ()
lockObject (CO p) = primIO $ prim__lockobject p

||| Unlocks a foreign callable code object to make it available to
||| garbage collection.
export %inline
unlockObject : HasIO io => CodeObject a -> io ()
unlockObject (CO p) = primIO $ prim__unlockobject p

||| An address (pointer) to a foreign callable Chez scheme code object.
public export
record Callback (a : Type) where
  constructor CB
  address : AnyPtr

export
nullCB : Callback a
nullCB = CB prim__getNullAnyPtr

||| Converts a foreign code object to a foreign callable function pointer.
export %inline
(.cb) : CodeObject a -> Callback a
(.cb) (CO ptr) = CB $ prim__foreign_callable_entry_point ptr

||| Returns the code object associated with a foreign callable function
||| pointer.
export %inline
(.co) : Callback a -> CodeObject a
(.co) (CB ptr) = CO $ prim__foreign_callable_code_object ptr

||| Locks the code object associated witha a function pointer.
export %inline
lockCB : HasIO io => Callback a -> io ()
lockCB cb = lockObject cb.co

||| Unlocks the code object associated witha a function pointer.
export %inline
unlockCB : HasIO io => Callback a -> io ()
unlockCB cb =
  case prim__nullAnyPtr cb.address of
    0 => unlockObject cb.co
    _ => pure ()

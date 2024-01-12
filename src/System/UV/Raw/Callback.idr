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

export %foreign "scheme:foreign-callable-entry-point"
prim__foreign_callable_entry_point : AnyPtr -> AnyPtr

export %foreign "scheme:(lambda (x) (foreign-callable #f (lambda (cb0) ((x cb0) #f)) (void*) void))"
prim__ptrCB : (AnyPtr -> PrimIO ()) -> PrimIO AnyPtr

export %foreign "scheme:(lambda (x) (foreign-callable #f (lambda (cb0 cb1) (((x cb0) cb1) #f)) (void* unsigned-32) void))"
prim__ptrUintCB : (AnyPtr -> Bits32 -> PrimIO ()) -> PrimIO AnyPtr

export %foreign "scheme:(lambda (x) (foreign-callable #f (lambda (cb0 cb1) (((x cb0) cb1) #f)) (void* integer-32) void))"
prim__ptrIntCB : (AnyPtr -> Int32 -> PrimIO ()) -> PrimIO AnyPtr

export %foreign "scheme:(lambda (x) (foreign-callable #f (lambda (cb0 cb1 cb2) ((((x cb0) cb1) cb2) #f)) (void* integer-32 void*) void))"
prim__ptrIntPtrCB : (AnyPtr -> Int32 -> AnyPtr -> PrimIO ()) -> PrimIO AnyPtr

export %foreign "scheme:(lambda (x) (foreign-callable #f (lambda (cb0 cb1 cb2) ((((x cb0) cb1) cb2) #f)) (void* unsigned-32 void*) void))"
prim__ptrUintPtrCB : (AnyPtr -> Bits32 -> AnyPtr -> PrimIO ()) -> PrimIO AnyPtr

export %foreign "scheme:(lambda (x) (foreign-callable #f (lambda (cb0 cb1 cb2 cb3) (((((x cb0) cb1) cb2) cb3) #f)) (void* unsigned-32 void* void*) void))"
prim__ptrIntPtrPtrCB : (AnyPtr -> Int32 -> AnyPtr -> AnyPtr -> PrimIO ()) -> PrimIO AnyPtr

--------------------------------------------------------------------------------
-- Low-level stuff
--------------------------------------------------------------------------------

export
lockAnyPtr : HasIO io => AnyPtr -> io ()
lockAnyPtr p =
  case prim__nullAnyPtr p of
    0 => primIO (prim__lockobject p)
    _ => pure ()

export
unlockAnyPtr : HasIO io => AnyPtr -> io ()
unlockAnyPtr p =
  case prim__nullAnyPtr p of
    0 => primIO (prim__unlockobject $ prim__foreign_callable_code_object p)
    _ => pure ()

export
ptrCB : HasIO io => (Ptr t -> IO ()) -> io AnyPtr
ptrCB f = do
  co <- primIO $ prim__ptrCB (\x => toPrim $ f $ prim__castPtr x)
  primIO (prim__lockobject co)
  pure $ prim__foreign_callable_entry_point co

export
ptrUintCB : HasIO io => (Ptr t -> Bits32 -> IO ()) -> io AnyPtr
ptrUintCB f = do
  co <- primIO $ prim__ptrUintCB (\v,x => toPrim $ f (prim__castPtr v) x)
  primIO (prim__lockobject co)
  pure $ prim__foreign_callable_entry_point co

export
ptrIntCB : HasIO io => (Ptr t -> Int32 -> IO ()) -> io AnyPtr
ptrIntCB f = do
  co <- primIO $ prim__ptrIntCB (\x,v => toPrim $ f (prim__castPtr x) v)
  primIO (prim__lockobject co)
  pure $ prim__foreign_callable_entry_point co

export
ptrIntPtrCB : HasIO io => (Ptr t -> Int32 -> Ptr u -> IO ()) -> io AnyPtr
ptrIntPtrCB f = do
  co <- primIO $ prim__ptrIntPtrCB
    (\x,v,y => toPrim $ f (prim__castPtr x) v (prim__castPtr y))
  primIO (prim__lockobject co)
  pure $ prim__foreign_callable_entry_point co

export
ptrIntPtrPtrCB : HasIO io => (Ptr t -> Int32 -> Ptr u -> Ptr v -> IO ()) -> io AnyPtr
ptrIntPtrPtrCB f = do
  co <- primIO $ prim__ptrIntPtrPtrCB
    (\x,v,y,z => toPrim $ f (prim__castPtr x) v (prim__castPtr y) (prim__castPtr z))
  primIO (prim__lockobject co)
  pure $ prim__foreign_callable_entry_point co

export
ptrUintPtrCB : HasIO io => (Ptr t -> Bits32 -> Ptr u -> IO ()) -> io AnyPtr
ptrUintPtrCB f = do
  co <- primIO $ prim__ptrUintPtrCB
    (\x,v,y => toPrim $ f (prim__castPtr x) v (prim__castPtr y))
  primIO (prim__lockobject co)
  pure $ prim__foreign_callable_entry_point co

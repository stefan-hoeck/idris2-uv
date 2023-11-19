module System.UV.File

import System.UV.Loop
import System.UV.Util

%default total

export
data FilePtr : Type where

public export
record UFile where
  [noHints]
  constructor MkFile
  signal : Ptr FilePtr

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_alloc_file")
prim__allocFile : PrimIO (Ptr FilePtr)

%foreign (idris_uv "uv_free_file")
prim__freeFile : Ptr FilePtr -> PrimIO ()

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

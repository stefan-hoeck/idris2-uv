module System.UV.Handle

import System.UV.Loop
import System.UV.Pointer
import System.UV.Util
import System.UV.Resource
import public System.UV.Raw.Handle

%default total

||| Closes the given `uv_handle_t` and releases the memory allocated for it.
export %inline
releaseHandle : 
     {auto has   : HasIO io}
  -> {auto 0 prf : PCast t Handle}
  -> Ptr t
  -> io ()
releaseHandle p = uv_close p $ freePtr

||| Manage a `uv_handle_t` as a resource that can be released.
|||
||| Upon invoking `release` on the returned `Resource`, the handle
||| will be closed by calling `uv_close` and release from memory
||| in the callback passed to `uv_close`.
export %inline
manageHandle : 
     {auto has   : HasIO io}
  -> {auto 0 prf : PCast t Handle}
  -> Ptr t
  -> io Resource
manageHandle = handle . releaseHandle

module System.UV.Handle

-- import System.UV.Async
-- import System.UV.Pointer
-- import public System.UV.Raw.Handle
--
-- %default total
--
-- ||| Closes the given `uv_handle_t` and releases the memory allocated for it.
-- export %inline
-- handle :
--      {auto has   : HasIO io}
--   -> {auto 0 prf : PCast t Handle}
--   -> Ptr t
--   -> io Resource
-- handle p = mkResource $ uv_close p $ freePtr

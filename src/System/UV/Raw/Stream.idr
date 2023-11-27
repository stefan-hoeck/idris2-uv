module System.UV.Raw.Stream

import System.UV.Raw.Handle
import System.UV.Raw.Loop
import System.UV.Raw.Pointer
import System.UV.Raw.Util

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign (idris_uv "uv_shutdown")
prim__uv_shutdown :
     Ptr Shutdown
  -> Ptr Stream
  -> (Ptr Shutdown -> Int32 -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_listen")
prim__uv_listen :
     Ptr Stream
  -> (backlog : Int32)
  -> (Ptr Stream -> Int32 -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_accept")
prim__uv_accept : (server, client : Ptr Stream) -> PrimIO Int32

%foreign (idris_uv "uv_read_start")
prim__uv_read_start :
     Ptr Stream
  -> (allocCb : Ptr Handle -> Bits32 -> Ptr Buf -> PrimIO ())
  -> (readCb  : Ptr Stream -> Int32 -> Ptr Buf -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_read_stop")
prim__uv_read_stop : Ptr Stream -> PrimIO Int32

%foreign (idris_uv "uv_write")
prim__uv_write : 
     Ptr Write
  -> Ptr Stream
  -> Ptr Buf
  -> (nbufs : Bits32)
  -> (Ptr Write -> Int32 -> PrimIO ())
  -> PrimIO Int32

%foreign (idris_uv "uv_is_readable")
prim__uv_is_readable : Ptr Stream -> PrimIO Int32 

%foreign (idris_uv "uv_is_writable")
prim__uv_is_writable : Ptr Stream -> PrimIO Int32 

%foreign (idris_uv "uv_stream_set_blocking")
prim__uv_stream_set_blocking: Ptr Stream -> Int32 -> PrimIO Int32

%foreign (idris_uv "uv_stream_get_write_queue_size")
prim__uv_get_write_queue_size: Ptr Stream -> PrimIO Bits32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

parameters {auto has : HasIO io}

  ||| Shutdown the outgoing (write) side of a duplex stream.
  ||| It waits for pending write requests to complete. The handle should
  ||| refer to a initialized stream.  req should be an uninitialized shutdown
  ||| request struct. The cb is called after shutdown is complete.
  export %inline
  uv_shutdown :
       (req : Ptr Shutdown)
    -> (str : Ptr t)
    -> {auto 0 cst : PCast t Stream}
    -> (Ptr Shutdown -> Int32 -> IO ())
    ->  io Int32
  uv_shutdown sd str act =
    primIO $ prim__uv_shutdown sd (castPtr str) $ \p,n => toPrim $ act p n

  ||| Start listening for incoming connections.
  ||| backlog indicates the number of connections the kernel might queue,
  ||| same as listen(2). When a new incoming connection is received
  ||| the uv_connection_cb callback is called.
  export %inline
  uv_listen :
       (str : Ptr t)
    -> {auto 0 cst : PCast t Stream}
    -> (backlog : Int32)
    -> (Ptr Stream -> Int32 -> IO ())
    ->  io Int32
  uv_listen str bl act =
    primIO $ prim__uv_listen (castPtr str) bl $ \p,n => toPrim $ act p n

  export %inline
  uv_accept :
       (server : Ptr s)
    -> (client : Ptr t)
    -> {auto 0 csts : PCast s Stream}
    -> {auto 0 cstt : PCast t Stream}
    ->  io Int32
  uv_accept ser cli = primIO $ prim__uv_accept (castPtr ser) (castPtr cli)

  ||| Read data from an incoming stream.
  ||| The `readCB` callback will be made several times until there is
  ||| no more data to read or `readstop` is called.
  export %inline
  uv_read_start :
       Ptr t
    -> {auto 0 cstt : PCast t Stream}
    -> (allocCb : Ptr Handle -> Bits32 -> Ptr Buf -> IO ())
    -> (readCb  : Ptr Stream -> Int32 -> Ptr Buf -> IO ())
    ->  io Int32
  uv_read_start str allocCB readCB =
    primIO $
      prim__uv_read_start
        (castPtr str)
        (\h,s,buf => toPrim $ allocCB h s buf)
        (\h,s,buf => toPrim $ readCB h s buf)

  ||| Stop reading data from the stream. The uv_read_cb callback will no longer
  ||| be called.
  ||| 
  ||| This function is idempotent and may be safely called on a stopped stream.
  ||| 
  ||| This function will always succeed; hence, checking its return value 
  ||| is unnecessary. A non-zero return indicates that finishing releasing
  ||| resources may be pending on the next input event on that TTY on Windows,
  ||| and  does not indicate failure.
  export %inline
  uv_read_stop : Ptr t -> {auto 0 cstt : PCast t Stream} -> io ()
  uv_read_stop str = ignore $ primIO $ prim__uv_read_stop (castPtr str)

  ||| Write data to stream. Buffers are written in order. Example:
  export %inline
  uv_write : 
       Ptr Write
    -> Ptr t
    -> {auto 0 cstt : PCast t Stream}
    -> Ptr Buf
    -> (nbufs : Bits32)
    -> (Ptr Write -> Int32 -> IO ())
    ->  io Int32
  uv_write wr str buf nbufs act =
    primIO $ prim__uv_write wr (castPtr str) buf nbufs $ \p,n => toPrim (act p n)

  export %inline
  uv_is_readable : Ptr t -> (0 _ : PCast t Stream) => io Bool
  uv_is_readable p = int32ToBool <$> primIO (prim__uv_is_readable $ castPtr p)

  export %inline
  uv_is_writable : Ptr t -> (0 _ : PCast t Stream) => io Bool
  uv_is_writable p = int32ToBool <$> primIO (prim__uv_is_writable $ castPtr p)

  export %inline
  uv_stream_set_blocking : Ptr t -> (0 _ : PCast t Stream) => Bool ->  io Int32
  uv_stream_set_blocking p b =
    primIO $ prim__uv_stream_set_blocking (castPtr p) (boolToInt32 b)

  export %inline
  uv_get_write_queue_size: Ptr t -> (0 _ : PCast t Stream) => io Bits32
  uv_get_write_queue_size p = primIO $ prim__uv_get_write_queue_size (castPtr p)

module System.UV.Stream

import System.FFI
import System.UV.Error
import System.UV.File
import System.UV.Handle
import System.UV.Loop
import System.UV.Pointer
import System.UV.Util

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

||| Shutdown the outgoing (write) side of a duplex stream.
||| It waits for pending write requests to complete. The handle should
||| refer to a initialized stream.  req should be an uninitialized shutdown
||| request struct. The cb is called after shutdown is complete.
export %inline
shutdown :
     (req : Ptr Shutdown)
  -> (str : Ptr t)
  -> {auto 0 cst : PCast t Stream}
  -> (Ptr Shutdown -> Int32 -> IO ())
  -> UVIO ()
shutdown sd str act =
  primUV $ prim__uv_shutdown sd (castPtr str) $ \p,n => toPrim $ act p n

||| Start listening for incoming connections.
||| backlog indicates the number of connections the kernel might queue,
||| same as listen(2). When a new incoming connection is received
||| the uv_connection_cb callback is called.
export %inline
listen :
     (str : Ptr t)
  -> {auto 0 cst : PCast t Stream}
  -> (backlog : Int32)
  -> (Ptr Stream -> Int32 -> IO ())
  -> UVIO ()
listen str bl act =
  primUV $ prim__uv_listen (castPtr str) bl $ \p,n => toPrim $ act p n

export %inline
accept :
     (server : Ptr s)
  -> (client : Ptr t)
  -> {auto 0 csts : PCast s Stream}
  -> {auto 0 cstt : PCast t Stream}
  -> UVIO ()
accept ser cli = primUV $ prim__uv_accept (castPtr ser) (castPtr cli)

||| Read data from an incoming stream.
||| The `readCB` callback will be made several times until there is
||| no more data to read or `readstop` is called.
export %inline
readStart :
     Ptr t
  -> {auto 0 cstt : PCast t Stream}
  -> (allocCb : Ptr Handle -> Bits32 -> Ptr Buf -> IO ())
  -> (readCb  : Ptr Stream -> Int32 -> Ptr Buf -> IO ())
  -> UVIO ()
readStart str allocCB readCB =
  primUV $
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
readStop : HasIO io => Ptr t -> {auto 0 cstt : PCast t Stream} -> io ()
readStop str = ignore $ primIO $ prim__uv_read_stop (castPtr str)

||| Write data to stream. Buffers are written in order. Example:
export %inline
write : 
     Ptr Write
  -> Ptr t
  -> {auto 0 cstt : PCast t Stream}
  -> Ptr Buf
  -> (nbufs : Bits32)
  -> (Ptr Write -> Int32 -> IO ())
  -> UVIO ()
write wr str buf nbufs act =
  primUV $ prim__uv_write wr (castPtr str) buf nbufs $ \p,n => toPrim (act p n)

export %inline
isReadable : HasIO io => Ptr t -> (0 _ : PCast t Stream) => io Bool
isReadable p = int32ToBool <$> primIO (prim__uv_is_readable $ castPtr p)

export %inline
isWritable : HasIO io => Ptr t -> (0 _ : PCast t Stream) => io Bool
isWritable p = int32ToBool <$> primIO (prim__uv_is_writable $ castPtr p)

export %inline
streamSetBlocking : Ptr t -> (0 _ : PCast t Stream) => Bool -> UVIO ()
streamSetBlocking p b =
  primUV $ prim__uv_stream_set_blocking (castPtr p) (boolToInt32 b)

export %inline
getWriteQueueSize: HasIO io => Ptr t -> (0 _ : PCast t Stream) => io Bits32
getWriteQueueSize p = primIO $ prim__uv_get_write_queue_size (castPtr p)

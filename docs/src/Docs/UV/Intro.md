# libuv: A Library for asynchronous IO

C library *libuv* is a library for event-driven asynchronous
programming. It is used - and was primarily developed for use -
by Node.js. This project, idris2-uv, provides bindings the
functionality of libuv to make its asynchronous model available
to Idris2.

In this tutorial, I am going to demonstrate with a couple of
example applications, why asynchronous I/O is a very powerful
concept. However, I am not going to cover every aspect of libuv.
Fortunately, libuv is a very well documented library. Documentation
with many example applications and implementation details
can be found [here](http://docs.libuv.org/en/v1.x/).

Before we begin, please note that this library is organized
in two parts: Submodules of `System.UV.Raw` contain the raw
FFI bindings to the underlying C library. Use these if you are
planning to write your own abstractions on top of libuv. Note,
however, that they come without the usual safety measures available
to Idris programmers in general: Pointer will need to allocated
and freed explicitly, and the types used in the raw bindings
are mostly restricted to those than can be passed to and from the
C foreign function interface (FFI).

## A couple of basic Examples

In accordance to what was said about manual,
resource management: Here is the *hello world* of libuv.

```idris
module Docs.UV.Intro

import Data.IORef
import System
import System.UV
import System.UV.File
import System.UV.Raw.Idle
import System.UV.Raw.Loop
import System.UV.Raw.Pipe
import System.UV.Raw.TCP
import System.UV.Raw.Signal
import System.UV.Raw.Stream

%default total

loopExample : IO ()
loopExample = do
  loop     <- mallocPtr Loop
  resInit  <- uv_loop_init loop
  resRun   <- uv_run loop UV_RUN_DEFAULT
  resClose <- uv_loop_close loop
  freePtr loop
```

While this an especially boring version of *hello world* (it
doesn't even generate any output but just terminates silently),
it demonstrates a few basic concepts.

First, when we use the raw bindings, we have to allocate and
free pointers on regular occasions. That's tedious and error
prone, so we will want to have a layer of sanity on top of
that. We will talk about that further below.

Second, most methods in libuv return a status code, that typically
is zero if all went well and negative in case of an error. We may
want to have proper error handling on top of this.

Finally, the loop. After we allocated and initialized the loop
pointer (of type `Ptr Loop`) in the code above, we started
running it with `uv_run`. There are a couple of important
notes about running a loop: First of all, the event loop is
single-threaded, that is, our program code is executed in
a single thread. As such, it is safe to make use of shared
mutable state where this is needed. However, the event loop
also asynchronous and non-blocking. This means, that IO
actions we request from the event loop are not blocking
the current thread, but are registered at the event loop
and executed in the next cycle of the loop. Internally, libuv
makes use of threads for asynchronous file access, but this
has no effect on the surface program we write except making it
fast and responsive.

The example above can be somewhat simplified by using the default
event loop, which is what you typically want. Here's the modified
code:

```idris
defaultLoopExample : IO ()
defaultLoopExample = do
  loop     <- uv_default_loop
  resRun   <- uv_run loop UV_RUN_DEFAULT
  resClose <- uv_loop_close loop
  pure ()
```

### Idling in a Loop

In the next example we write our first libuv application that
actually produces some output. For this, we must quickly talk
about handles and requests. In libuv, we want to get notified
about certain events. For this, we register handles and requests
at the event loop. Handles are long-lived object while requests
are typically short-lived operations on handles. This distinction
will become more clear in due time.

Let's come up with a first example of an asynchronous program:
We use the *idle* handle, which gets notified on every iteration
of the event loop:

```idris
checkCounter : (stop : Integer) -> IORef Integer -> Ptr Idle -> IO ()
checkCounter stop ref handle = do
  modifyIORef ref (+1)
  v <- readIORef ref
  when (v `mod` 1000 == 0) (putStrLn "Counter is at \{show v}")
  when (v >= stop) (ignore $ uv_idle_stop handle)

idleExample : IO ()
idleExample = do
  loop     <- uv_default_loop
  handle   <- mallocPtr Idle
  _        <- uv_idle_init loop handle
  ref      <- newIORef 0
  _        <- uv_idle_start handle (checkCounter 100_000 ref)
  _        <- uv_run loop UV_RUN_DEFAULT
  _        <- uv_loop_close loop
  freePtr handle

-- main : IO ()
-- main = idleExample
```

You can try the example above by uncommenting the `main` function
and running this file with `pack exec docs/src/Docs/UV/Intro.md`.
You will see that we run 100'000 iterations of the event loop,
printing some output at certain occasions and stopping the *idle*
handle at the end.

This is an important concept in libuv: The main event loop runs until
there are no more registered handles to run. Then it stops and the program
ends.

### Catching Signals

Let's another layer of complexity but adding a second way to abort our
application: We repeat the `idleExample` but with a larger value for
the upper bound of the counter. In addition, we add a handle to catch
`SIGINT` (pressing `Ctrl-C` at the console) that will also abort
the app:

```idris
stop : Ptr Idle -> Ptr Signal -> Int32 -> IO ()
stop idl _ sig = do
  putStrLn "Application interrupted by signal \{show sig} (SIGINT)."
  ignore $ uv_idle_stop idl
  putStrLn "Goodbye."

signalExample : IO ()
signalExample = do
  loop       <- uv_default_loop

  -- setting up the idler
  idler      <- mallocPtr Idle
  _          <- uv_idle_init loop idler
  ref        <- newIORef 0
  _          <- uv_idle_start idler (checkCounter 10_000_000 ref)

  -- setting up the signal
  killSwitch <- mallocPtr Signal
  _          <- uv_signal_init loop killSwitch
  _          <- uv_unref killSwitch
  _          <- uv_signal_start killSwitch (stop idler) uv_sigint

  -- running the app
  _          <- uv_run loop UV_RUN_DEFAULT

  -- cleaning up
  _          <- uv_loop_close loop
  freePtr idler
  freePtr killSwitch

-- main : IO ()
-- main = signalExample
```

If you run the application above, it will print lots of output for a
couple of seconds before it stops. However, if you press `Ctrl-C` at
the terminal, the application will abort immediately. While the code
above is a bit verbose, the concepts shown so far are already quite
powerful.

Everything about setting up the kill switch is similar to what we did with
the idler, with one exception: The call to `uv_unref`. In libuv, the event
loop runs as long as there are active *and* referenced handles. We
un-reference the kill switch, because the idler should not be responsible
of stopping all other handles. Feel free to remove the call to `uv_unref`
and run the application again: It will not terminate even after the idler
has finished. It won't even stop if you press `Ctrl-C`, because in the
current version, the kill switch does not terminate itself.

So, typically this is the behavior we want: An application should
stop when it either has finished with its main task *or* when
it was manually aborted. And a nice way to achieve this is to un-reference
all supporting handles.

### Reading Files

We are now ready to asynchronously read the content of a file and print
it to standard output. And while the simple examples above were a bit
tedious to write with all that manual allocating and freeing of pointers,
we will now see that raw file input and output is a different kind of
beast. Here's the general structure

```idris
onOpen : Ptr Loop -> Ptr Fs -> IO ()

catFile : Ptr Loop -> String -> IO Int32
catFile loop path = do
  openFS <- mallocPtr Fs
  uv_fs_open loop openFS path uv_rdonly 0 (onOpen loop)

fileExample : IO ()
fileExample = do
  (_::p::_) <- getArgs | _ => die "Invalid number of arguments"
  loop <- uv_default_loop
  _    <- catFile loop p
  _    <- uv_run loop UV_RUN_DEFAULT
  ignore $ uv_loop_close loop

-- main : IO ()
-- main = fileExample
```

That doesn't look too bad: We get the file path to read as a
command line argument, setup the main loop, asynchronously open a
file and invoke a callback once the file is ready.
Let's implement `onOpen` next.

```idris
onRead : Ptr Loop -> Ptr Buf -> Int32 -> Ptr Fs -> IO ()

onOpen loop openFS = do
  res <- uv_fs_get_result openFS

  -- releasing resources
  uv_fs_req_cleanup openFS
  freePtr openFS

  -- checking result: < 0 means an error occured, otherwise, it's a
  -- file handle
  if res < 0
     then putStrLn "Error when reading: \{uv_strerror res}"
     else do
       putStrLn "File opened successfully for reading"
       -- allocating the `uv_fs_t` for reading
       readFS <- mallocPtr Fs
       -- allocating the read buffer
       buf    <- mallocBuf 0xffff
       ignore $ uv_fs_read loop readFS res buf 1 0 (onRead loop buf res)
```

So, that's quite a lot of code for something as "simple" as reading a file.
And we are not even done yet. And still, this shows all the kind of allocating
and book-keeping that's necessary when doing this kind of stuff in a
language like C. Idris is not C, and we will be able to add a layer of
sanity on top of all of this, but you might not like that layer and
want to implement your own abstractions, so it's good to see how
everything works under the hood.

We first note, that the result of the file opening request is stored in
the request's `result` field: This is an integer that's either a file
handle or an error code (if the value is less than zero). In case of
an error, we can get a proper error message with `uv_strerror`. If all
goes well, we have to issue a new asynchronous request. For this, we allocate
another request pointer (`readFS`). We also need to allocate a byte
array where the data read from the file can be stored: We allocate
65535 bytes of data with `mallocBuf`. Finally, we invoke `uv_fs_read`.
The two integer literals need some explanation: The `1` is the number
of buffers we are passing (`buf` is a pointer to `uv_buf`, so this could
also be pointing to an array of buffers), and the zero indicates the
file position we want to read from.

We still have to implement `onRead`. Let's do that next:

```idris
onRead loop buf file readFS = do
  res <- uv_fs_get_result readFS

  -- closing the file
  _ <- uv_fs_close_sync loop file

  -- releasing the file system request
  uv_fs_req_cleanup readFS
  freePtr readFS

  if res < 0
     then putStrLn "Error opening file: \{uv_strerror res}"
     else do
       putStrLn "Read \{show res} bytes of data\n"
       fsWrite <- mallocPtr Fs
       ignore $ uv_fs_write loop fsWrite 1 buf 1 (-1) $ \fs =>
         freeBuf buf >> freePtr fs
```

That's still more cleaning up of resources. In the end, we print the
data we read to *stdout* (file handle 1) at offset `-1` (the current
offset) and free the allocated buffer.

In order to to simplify things, we closed the file.
This will block the event loop but for simple one-off operations
like this, that's usually alright.
Otherwise, we'd have to allocate and free even more stuff.

Note, that we can run all file requests synchronously in libuv
by passing the `NULL` pointer as the callback. We have to provide
these version separately via the FFI, because we can't directly
send `NULL` in place of a callback function across the FFI.

### Observing Asynchronisity

It is quite illuminating to add an *idle* handle on top of
our file reading application. In the following version, we print
a short message on every iteration of the event loop. We make sure
the event loop stops when we are done with reading and writing
data by un-referencing the idler.

```idris
countIterations : IORef Nat -> IO ()
countIterations ref = do
  modifyIORef ref S
  v <- readIORef ref
  putStrLn "I'm at iteration \{show v} now."

fileExample2 : IO ()
fileExample2 = do
  (_::p::_) <- getArgs | _ => die "Invalid number of arguments"
  loop  <- uv_default_loop

  -- Setting up the idler
  ref   <- newIORef Z
  idler <- mallocPtr Idle
  _     <- uv_idle_init loop idler
  _     <- uv_idle_start idler (\_ => countIterations ref)
  _     <- uv_unref idler

  _     <- catFile loop p
  _     <- uv_run loop UV_RUN_DEFAULT
  _     <- uv_loop_close loop
  freePtr idler

-- main : IO ()
-- main = fileExample2
```

Running this will show you how many iterations of the event loop
pass before the file is opened, read, and written to the terminal.
On my machine, terminal output took the longest, so it's definitely
something we should consider to be doing asynchronously to keep
our application responsive.

### Streaming Standard Input

Below is a simple example of streaming data from a pipe (standard
input in this case, which has file handle zero): We read data from
standard input and echo it back to standard output.

For reasons of efficiency, we allocate a single buffer that we
keep reusing. This is incredibly efficient. For instance,
when piping the output of `cat` on a lengthy file into the
compiled program and redirecting standard output to a file
on disk, I can copy 2 GB of data in about 1.5 seconds on my
machine.

```idris
BufSize : Bits32
BufSize = 0xffff

allocBuf : Ptr Bits8 -> Ptr Handle -> Bits32 -> Ptr Buf -> IO ()
allocBuf cs _ _ buf = initBuf buf cs BufSize

onStreamRead : Ptr Loop -> Ptr Stream -> Int32 -> Ptr Buf -> IO ()
onStreamRead loop stream res buf = do
  if res < 0
     then when (res /= UV_EOF) (putStrLn "Error: \{uv_strerror res}")
     else setBufLen buf (cast res) >>
          ignore (uv_fs_write_sync loop 1 buf 1 (-1))

streamExample : IO ()
streamExample = do
  loop <- uv_default_loop

  pipe <- mallocPtr Pipe
  _    <- uv_pipe_init loop pipe False
  r    <- uv_pipe_open pipe 0
  cs   <- mallocPtrs Bits8 BufSize
  _    <- uv_read_start pipe (allocBuf cs) (onStreamRead loop)
  _    <- uv_run loop UV_RUN_DEFAULT
  ignore $ uv_loop_close loop

-- main : IO ()
-- main = streamExample
```

Two new concepts appear in the code example above: Initialization of pipes
with `uv_pipe_open` and checking for the end of input by comparing
the reading result with `UV_EOF`. All other concepts have already been
explained before.

In addition, we used streams for the first time. In libuv, TCP sockets,
UDP sockets, and pipes for file I/O and inter process communication all
are treated as streams, and the unit of data is `uv_buf_t` represented
by `Ptr Buf` in Idris. It consists of a `base` field (a pointer to
bytes) and the length.

### A TCP Echo Server

Having seen a first example of input streams, it is not a big step to
implement our first TCP server: A server listening on local IP address
"0.0.0.0" and port 7000 that just echoes back the messages it gets
from its clients.

Below, we are setting up the skeleton of our applications. We need
callbacks for when we get a new connection from a client, when
we read data from the client, when we need to allocate memory
for the client message, and when we have written data to a client.

This is the core structure of a server application. The main work
happens in function `echoRead`, where we typically process the client
request and convert it to a response that will then be sent back
to the client.

```idris
allocEchoBuffer : Ptr Handle -> Bits32 -> Ptr Buf -> IO ()
allocEchoBuffer _ size buf = do
  cs <- mallocPtrs Bits8 size
  initBuf buf cs size

onNewConnection : Ptr Loop -> Ptr Stream -> Int32 -> IO ()

echoRead : Ptr Stream -> Int32 -> Ptr Buf -> IO ()

echoWrite : Ptr Buf -> Ptr Write -> Int32 -> IO ()
echoWrite buf req status = do
  freePtr buf
  freePtr req
  when (status < 0) (putStrLn "Write error \{uv_strerror status}")

stopEcho : Ptr Tcp -> Ptr Signal -> Int32 -> IO ()
stopEcho server _ sig = do
  putStrLn "Application interrupted by signal \{show sig} (SIGINT)."
  ignore $ uv_close_sync server
  putStrLn "Goodbye."

echoExample : IO ()
echoExample = do
  loop   <- uv_default_loop
  server <- mallocPtr Tcp
  _      <- uv_tcp_init loop server

  -- binding the server to local address 0.0.0.0 at port 7000
  addr   <- mallocPtr SockAddrIn
  _      <- uv_ip4_addr "0.0.0.0" 7000 addr
  _      <- uv_tcp_bind server addr 0

  -- start listening (this actually will start when we run the event loop)
  putStrLn "Listening on 0.0.0.0 port 7000"
  r      <- uv_listen server 128 (onNewConnection loop)

  -- setting up a kill switch
  kill   <- mallocPtr Signal
  _      <- uv_signal_init loop kill
  _      <- uv_unref kill
  _      <- uv_signal_start kill (stopEcho server) uv_sigint

  when (r < 0) (die "Listen error: \{uv_strerror r}")
  _      <- uv_run loop UV_RUN_DEFAULT

  freePtr server
  freePtr addr
```

Allocating data is straight forward as is cleaning up after we
have sent our response to the client. The main application
sets up a TCP socket at local address "0.0.0.0" on port 7000
plus a handler for `SIGINT`, which allows us to gracefully shutdown
the application.

Let's implement `onNewConnection` next:

```idris
onNewConnection loop server status =
  if status < 0
     then putStrLn "New connection error \{uv_strerror status}"
     else do
       putStrLn "Got a new connection."
       client <- mallocPtr Tcp
       _      <- uv_tcp_init loop client
       0      <- uv_accept server client | _ => uv_close client freePtr
       ignore $ uv_read_start client allocEchoBuffer echoRead
```

Upon receiving a client request, we setup and accept a new connection
with the client and start reading data from that connection. In
case of an error, the connection to the client is properly closed.

Finally, here's the implementation of `echoRead`:

```idris
echoRead client nread buf =
  if nread > 0
     then do
       putStrLn "Got \{show nread} bytes of data"
       req  <- mallocPtr Write
       wbuf <- mallocPtr Buf
       dat  <- getBufBase buf
       initBuf wbuf dat (cast nread)
       ignore $ uv_write req client wbuf 1 (echoWrite wbuf)
     else do
       putStrLn "Closing connection to client"
       dat <- getBufBase buf
       freePtr dat
       uv_close client freePtr
       when (nread /= UV_EOF) $ do
         putStrLn "Read error \{uv_strerror nread}"

-- main : IO ()
-- main = echoExample
```

If we got some data, we typically process it and send a response to
the client. Processing in this case is trivial, because we just
echo the request back to the client. As usual, we need to allocate
some bytes for setting up the write request and for sending the data.
We then invoke `uv_write`, which will asynchronously send our response
back to the client. When we reach the end of client input, we free
the allocated memory and close the connection on our end.

The application above as an important shortcoming: When we decide to
shut down our server, the application will only terminate after every
client session has ended. Since clients decide, when a session ends,
this might take a long time. In a real world server we'd want to
keep track of client sessions and close them on our end when we
shutdown the server.

### A TCP Client

Writing a TCP client is not much different from writing
a server:

```idris
onClientRead : Ptr Loop -> Ptr Stream -> Int32 -> Ptr Buf -> IO ()
onClientRead loop stream res buf = do
  if res < 0
     then when (res /= UV_EOF) (putStrLn "Error: \{uv_strerror res}") >>
          ignore (uv_close stream freePtr)
     else setBufLen buf (cast res) >>
          ignore (uv_fs_write_sync loop 1 buf 1 (-1))

  getBufBase buf >>= freePtr

onClientWrite : Ptr Loop -> Ptr Tcp -> Ptr Write -> Int32 -> IO ()
onClientWrite loop client write status = do
  freePtr write
  ignore $ uv_read_start client allocEchoBuffer (onClientRead loop)

onClientConnect : Ptr Loop -> Ptr Tcp -> Ptr Connect -> Int32 -> IO ()
onClientConnect loop client connect status = do
  freePtr connect
  if status < 0
     then putStrLn "New connection error: \{uv_strerror status}"
     else do
       putStrLn "Got a new connection."
       req  <- mallocPtr Write
       dat  <- fromString "Hello? Anybody out there?\n"
       ignore $ uv_write req client dat 1 (onClientWrite loop client)

clientExample : IO ()
clientExample = do
  loop   <- uv_default_loop
  socket <- mallocPtr Tcp
  _      <- uv_tcp_init loop socket

  -- binding the server to local address 0.0.0.0 at port 7000
  addr   <- mallocPtr SockAddrIn
  _      <- uv_ip4_addr "localhost" 7000 addr

  -- start listening (this actually will start when we run the event loop)
  putStrLn "Connecting to 0.0.0.0 port 7000"
  connect <- mallocPtr Connect
  r       <- uv_tcp_connect connect socket addr (onClientConnect loop socket)

  when (r < 0) (die "Connect error: \{uv_strerror r}")
  _      <- uv_run loop UV_RUN_DEFAULT

  freePtr addr

-- main : IO ()
-- main = clientExample
```

And while the above example might now (hopefully) be pretty clear, it's
also obvious that this kind of code is getting far too tedious to
write. So, the next step will be to factor out certain reoccurring
patterns and add a layer of proper immutable Idris types on top
of it all. That's for the second part of the tutorial.

<!-- vi: filetype=idris2:syntax=markdown
-->

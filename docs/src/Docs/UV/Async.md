# Monad `Async`

In this part of the documentation section, I am going to reimplement
parts of the introduction on top of the `Async` monad, which is a
powerful tool for setting up and running asynchronous computations.

We start with some imports and type aliases:

```idris
module Docs.UV.Async

import Data.IORef
import System
import System.File
import System.UV
import System.UV.Idle
import System.UV.Signal
import System.UV.Stream
import System.UV.Raw.Stream
import System.UV.TCP
import System.UV.Timer

0 DocIO : Type -> Type
DocIO = Async [UVError]

handles : All (\x => x -> Async [] ()) [UVError]
handles = [putStrLn . interpolate]

runDoc : (UVLoop => DocIO ()) -> IO ()
runDoc doc = runUV $ handle handles doc
```

So, `DocIO a` is an alias for `Async [UVError] a`, which is a computation
that will be run asynchronously on the libuv event loop. Asynchronous
computations can end in one of three outcomes: They can successfully
produce a result of type `a`, the can fail with one of the errors
given in their list, or they can be canceled internally or externally.

In addition, `Async` provides strong and safe resource management
capabilities, so a lot of the manual cleanup with had to do in the
introduction will just go away.

## A cancelable Counter

We start by reimplementing our cancelable counter example, but add
a slight twist to it: The counter itself should be run forever, but
it should be interrupted either by an external `SIGINT` event, or
after five seconds, whichever comes first.

Here's the code:

```idris
-- parameters {auto l : UVLoop}
--
--   checkCounter : IORef Integer -> DocIO (Maybe ())
--   checkCounter ref = do
--     modifyIORef ref (+1)
--     v <- readIORef ref
--     when (v `mod` 10000 == 0) (putOutLn "Counter is at \{show v}")
--     pure Nothing
--
--   idleExample : DocIO ()
--   idleExample = do
--     putStrLn "Hello World"
--     ref     <- newIORef 0
--     putStrLn "Starting the counter"
--     counter <- start $ onIdle (checkCounter ref)
--
--     res     <- raceAny [onSignal SIGINT, once 5000]
--
--     case res of
--       Here sig => putOutLn "Counter interrupted by \{show sig}"
--       _        => putOutLn "Counter interrupted by timeout"
--
--     putOutLn "Cancelling counter"
--     cancel

-- main : IO ()
-- main = runDoc $ do
--   putStrLn "Going to sleep"
--   race [sleep 2000, sleep 3100, sleep 500, ignore $ onSignal SIGINT]
--   putOutLn "Good morning"
```

First, we note that `Async` comes with an implementation of `MonadIO`,
so all `IO` actions can just be used with `Async` as well. We can therefore
still setup a mutable variable (`newIORef`) to be used in `checkCounter`.

The `checkCounter` routine is only slightly different: It no longer is
responsible of terminating the idler (although it could, as soon as it
would return a `Just`), and it uses the asynchronous `putOutLn` instead
of `putStrLn` to print to stdout.

The main application (`idleExample`), however, is quite a bit more
powerful than what we saw before. On the first line, we setup our
mutable reference, on the second, we start the idler. This will spawn
a new asynchronous computation (called a *fiber*), which will be run
independently of the current fiber on the event loop.

On the next line, we start two more fibers - a signal handler and
a timer - but we let them race each other: Whichever terminates
first will cancel the other and determine the outcome of `raceEither`.

Finally, we collect the result, print out some information and
cancel the current fiber, which will also cancel all its children,
namely the idler that is still running.

## Streaming a File

In this example we stream the content of one file to another.
However, we provide three possibilities how the computation might
stop: `SIGINT` is received, a ten seconds timeout occurs, or the
input stream is exhausted.

This shows, how we can conveniently set up a race of a
heterogeneous list of asynchronous computations.

```idris
parameters {auto l : UVLoop}
  fileStreamExample : DocIO ()
  fileStreamExample = do
    (_::p::_) <- getArgs | _ => putErrLn "Invalid number of arguments"
    v <- use1 (fsOpen "out" (WRONLY <+> CREAT) 0o644) $ \f =>
           raceAny
             [ onSignal SIGINT
             , sleep 10000
             , streamFile p 0xffff $ writeBytes f
             ]

    case v of
      Here s         => putOutLn "Stream interrupted by \{show s}"
      There (Here _) => putOutLn "Stream interrupted by timeout"
      _              => putOutLn "Stream exhausted."

main : IO ()
main = runDoc fileStreamExample
```

## An echo Server

In this last example, we again set up a simple echo server.
This time, however, the server gracefully closes all client
connections before shutting down (which happens, when
`SIGINT` is received).

```idris
-- parameters {auto l : UVLoop}
--   onConnection : AllocCB -> Ptr Stream -> DocIO (Maybe ())
--   onConnection ac server = do
--     putOutLn "Got a connection"
--     client <- acceptTcp server
--     _      <- start $ streamReadWrite ac client $ \case
--       Done     => pure (Just ())
--       Data val => write client val $> Nothing
--       Err x    => throw x
--     pure Nothing
--
--   echo : DocIO ()
--   echo = do
--     ac <- sizedAlloc 0xffff
--     server <- start $ listenTcp "0.0.0.0" 7000 $ \case
--       Left err  => putErrLn "Error when receiving request: \{err}" $> Nothing
--       Right srv => onConnection ac srv
--
--     ignore $ onSignal SIGINT
--     putOutLn "Shutting down server..."
--     cancel
--
-- main : IO ()
-- main = runDoc echo
```

<!-- vi: filetype=idris2:syntax=markdown
-->

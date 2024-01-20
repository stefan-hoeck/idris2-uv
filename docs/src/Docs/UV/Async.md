# Monad `Async`

In this part of the documentation section, I am going to reimplement
parts of the introduction on top of the `Async` monad, which is a
powerful tool for setting up and running asynchronous computations.

We start with some imports and type aliases:

```idris
module Docs.UV.Async

import IO.Async.Event
import System
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
parameters {auto l : UVLoop}
  timerExample : DocIO ()
  timerExample = onIdle (go 50)

    where
      go : Nat -> Event Nat -> DocIO ()
      go 0     m = pure ()
      go (S k) m = do
        n <- onEvent m
        putOutLn "At \{show $ S k}: Got \{show n} ticks"
        sleep 100
        go k m

-- main : IO ()
-- main = runDoc $ do
--   putStrLn "Going to sleep"
--   race [timerExample, ignore $ onSignal SIGINT]
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
             , streamFile p 0xfffff $ writeBytes f
             ]

    case v of
      Here s         => putOutLn "Stream interrupted by \{show s}"
      There (Here _) => putOutLn "Stream interrupted by timeout"
      _              => putOutLn "Stream exhausted."

-- main : IO ()
-- main = runDoc fileStreamExample
```

## An echo Server

In this last example, we again set up a simple echo server.
This time, however, the server gracefully closes all client
connections before shutting down (which happens, when
`SIGINT` is received).

```idris
parameters {auto l : UVLoop}
  onConnection : AllocCB -> Ptr Stream -> DocIO ()
  onConnection ac server = do
    putOutLn "Got a connection"
    bracket (acceptTcp server) echo shutdownStream

    where
      echoWrite : Ptr Tcp -> Buffer (ReadRes ByteString) -> DocIO ()
      echoWrite p buf = onEvent buf >>= echoWrite' . (<>> [])

        where
          echoWrite' : List (ReadRes ByteString) -> DocIO ()
          echoWrite' []            = echoWrite p buf
          echoWrite' (Done :: _)   = putOutLn "Done reading. Closing stream."
          echoWrite' (Data v :: t) = write p v >> echoWrite' t
          echoWrite' (Err x :: _)  =
            putErrLn "Error when reading from stream: \{show x}"

      echo : Ptr Tcp -> DocIO ()
      echo p = read ac p (echoWrite p)

  serve : AllocCB -> Buffer (Either UVError $ Ptr Stream) -> DocIO ()
  serve ac ev = (onEvent ev >>= traverse_ handleEv . (<>> [])) >> serve ac ev

    where
      handleEv : Either UVError (Ptr Stream) -> DocIO ()
      handleEv (Left x)  = putErrLn "Error while serving: \{x}"
      handleEv (Right x) = background $ onConnection ac x

  echo : DocIO ()
  echo = do
    ac <- sizedAlloc 0xffff
    race [listenTcp "0.0.0.0" 7000 (serve ac), ignore $ onSignal SIGINT]
    putOutLn "Shutting down server..."

main : IO ()
main = runDoc echo
```

<!-- vi: filetype=idris2:syntax=markdown
-->

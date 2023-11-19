module Main

import Data.IORef
import System.UV

stopAll : Timer -> Signal -> IO ()
stopAll ti si = do
  putStrLn "This is the end. Goodbye!"
  endTimer ti
  endSignal si

timer : IORef Nat -> IO ()
timer ref = do
  v <- readIORef ref
  writeIORef ref (S v)
  putStrLn "Timer \{show v}"

main : IO ()
main = do
  n  <- newIORef Z
  lp <- defaultLoop
  ti <- initTimer lp
  si <- initSignal lp
  _  <- onTimer ti (timer n) 5000 1000
  _  <- onSignal si (stopAll ti si) SIGINT
  putStrLn "Hello world"
  n  <- runLoop lp
  putStrLn "Terminated with \{show n}"

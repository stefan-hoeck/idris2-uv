module Main

import Data.IORef
import System
import System.UV

stopAll : List Timer -> Signal -> IO ()
stopAll ts si = do
  putStrLn "This is the end. Goodbye!"
  traverse_ endTimer ts
  endSignal si

timer : Loop => Nat -> IORef Nat -> IO ()
timer n ref = do
  v <- readIORef ref
  writeIORef ref (S v)
  putStrLn "Timer with a delay of \{show n} s: \{show v}"

main : IO ()
main = do
  n1  <- newIORef Z
  lp  <- defaultLoop
  si  <- initSignal
  t1  <- repeatedly 0 1700 (timer 1700 n1)
  t2  <- repeatedly 0 900  (timer 900  n1)
  t3  <- repeatedly 0 500  (timer 500  n1)
  t4  <- repeatedly 0 2300 (timer 2300 n1)

  let done = stopAll [t1,t2,t3,t4] si

  t   <- delayed 20000 done
  _   <- onSignal si done SIGINT
  putStrLn "Hello world"
  n  <- runLoop lp
  putStrLn "Terminated with \{show n}"

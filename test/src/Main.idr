module Main

import Data.IORef
import Flags
import Hedgehog
import System
import System.UV

timer : Loop => Nat -> IORef Nat -> IO ()
timer n ref = do
  v <- readIORef ref
  writeIORef ref (S v)
  putStrLn "Timer with a delay of \{show n} s: \{show v}"

main : IO ()
main = do
  n1  <- newIORef Z
  lp  <- defaultLoop
  t1  <- repeatedly 0 1700 (timer 1700 n1)
  t2  <- repeatedly 0 900  (timer 900  n1)
  t3  <- repeatedly 0 500  (timer 500  n1)
  t4  <- repeatedly 0 2300 (timer 2300 n1)

  t   <- delayed 5000 $ traverse_ endTimer [t1,t2,t3,t4]
  putStrLn "Hello world"
  n  <- runLoop lp
  putStrLn "Terminated with \{show n}"
  test
    [ Flags.props ]

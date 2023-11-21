module Main

import Control.Monad.Either
import Data.Buffer.Indexed
import Data.ByteString
import Data.IORef
import Flags
import Hedgehog
import System
import System.UV
import System.UV.File
import System.UV.File.Flags

timer : Loop => Nat -> IORef Nat -> IO ()
timer n ref = do
  v <- readIORef ref
  writeIORef ref (S v)
  putStrLn "Timer with a delay of \{show n} s: \{show v}"

processRes : IORef Nat -> (s : StreamRes ByteString) -> IO (StreamResp s)
processRes ref (Err x) = putStrLn "\{x}"
processRes ref Empty   = putStrLn "Stream exhausted."
processRes ref (Val x) = do
  modifyIORef ref (+ length x)
  tot <- readIORef ref
  putStrLn "Processed: \{show $ length x} bytes (\{show tot} total)" $> Cont

run : Loop => UVIO ()
run = do
  n1 <- newIORef Z
  rs <- sequence [ repeatedly 0 1700 (timer 1700 n1)
                 , repeatedly 0 900  (timer 900  n1)
                 , repeatedly 0 500  (timer 500  n1)
                 , repeatedly 0 2300 (timer 2300 n1)
                 ]

  tot <- newIORef Z
  stream "/data/gundi/googlebooks/googlebooks-eng-all-1gram-20120701-a" 0xffff (processRes tot)
          
  pure ()

main : IO ()
main = runUV run >> test [ Flags.props ]

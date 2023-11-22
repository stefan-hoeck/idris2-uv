module Timer

import System.UV

run : Loop => UVIO ()
run = do
  ti <- mallocHandle TIMER
  timerInit ti
  timerStart ti (\_ => putStrLn "timer fired!") 1000 0

export
main : IO ()
main = runUV run

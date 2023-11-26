module Timer

import System.UV

run : Loop => UVIO ()
run = ignore $ delayed 1000 (putOutLn "timer fired")

export
main : IO ()
main = runUV run

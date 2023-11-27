module Timer

import System.UV

run : UVLoop => UVIO ()
run = ignore $ delayed 1000 (runUVIO $ putOutLn "timer fired")

export
main : IO ()
main = runUV run

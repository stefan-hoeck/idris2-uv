module Main

import Flags
import Hedgehog
import Pointer
import Timer

main : IO ()
main = do
  Timer.main
  Pointer.run
  test [ Flags.props ]

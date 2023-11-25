module Main

import Hedgehog
import Flags
import Pointer

main : IO ()
main = do
  Pointer.run
  test [ Flags.props ]

module Main

import Flags
import Hedgehog
import System.UV

main : IO ()
main = test [ Flags.props ]

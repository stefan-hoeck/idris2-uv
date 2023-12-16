module System.Rx.Core

import Data.IORef
import System.Rx.Msg
import System.Rx.Sink
import System.Rx.Source

%default total

--------------------------------------------------------------------------------
-- Sinks
--------------------------------------------------------------------------------


public export
0 Pip : (es,fs : List Type) -> (a,b : Type) -> Type
Pip es fs a b = (Snk es a, Src fs b)

public export
record Pipe (es,fs : List Type) (a,b : Type) where
  constructor MkPipe
  mkPipe : IO (Pip es fs a b)

infixl 1 |>, |>>, >>>

infixr 1 >-

export
(|>) : Source es a -> Pipe es fs a b -> Source fs b
MkSource s |> MkPipe p = MkSource $ do
  srv        <- s
  (snk, src) <- p
  snk srv
  pure src

covering export
(|>>) : Source es a -> Sink es a -> IO ()
MkSource mso |>> MkSink msi = do
  srv <- mso
  snk <- msi forever
  snk srv

export
(>-) : Pipe es fs a b -> Sink fs b -> Sink es a
MkPipe p >- MkSink s = MkSink $ \fuel => do
  (snk,src) <- p
  f         <- s fuel
  f src
  pure snk

export
(>>>) : Pipe es fs a b -> Pipe fs gs b c -> Pipe es gs a c
MkPipe p1 >>> MkPipe p2 = MkPipe $ do
  (snk1,src1) <- p1
  (snk2,src2) <- p2
  snk2 src1
  pure (snk1,src2)

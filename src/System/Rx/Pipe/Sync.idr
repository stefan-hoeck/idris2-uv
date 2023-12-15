module System.Rx.Pipe.Sync

import Data.Buffer.Indexed
import Data.ByteString
import Data.ByteVect
import Data.DPair
import Data.IORef
import Data.Maybe
import System.Rx.Core
import System.Rx.Msg
import System.Rx.Sink
import System.Rx.Source

%default total

--------------------------------------------------------------------------------
-- General synchronous pipe.
--------------------------------------------------------------------------------

-- implementation of the downstream side of a synchronous pipe
syncSrc :
     SinkRef es a
 -> ((m : Msg es a) -> IO (ValidAfter m fs b))
 -> Src fs b
syncSrc ref f Nothing  = close ref
syncSrc ref f (Just g) = request ref $ \m1 => do
  Element m2 _ <- f m1
  when (isTerminal m1) (abort ref) -- upstream terminated, release resources
  when (isTerminal m2) (close ref) -- we terminated, send `Nothing` upstream
  g m2

||| Synchronous, sequential, and potentially effectful conversion
||| of messages.
|||
||| Since the result is of type `ValidAfter m fs b`, we can do error
||| handling here and we can abort early, but we cannot continue after
||| upstream has terminated.
|||
||| Most simple, sequential pipes are implemented via this function.
export
syncPipe :
     (convert : IO ((m : Msg es a) -> IO (ValidAfter m fs b)))
  -> Pipe es fs a b
syncPipe convert = MkPipe $ do
  conv <- convert
  ref  <- sinkRef es a (pure ())
  pure (sink ref, syncSrc ref conv)

--------------------------------------------------------------------------------
-- Pipes operating on lists of values
--------------------------------------------------------------------------------

||| Pure version of `syncPipe`.
export
mappingPipe : ((m : Msg es a) -> ValidAfter m fs b) -> Pipe es fs a b
mappingPipe f = syncPipe . pure $ \x => pure $ f x

||| A pipe operating on the chunks in messages.
export %inline
listPipe : (List a -> List b) -> Pipe es es a b
listPipe f =
  mappingPipe $ \case
    Next vs => vnext (f vs)
    Done vs => vdone (f vs)
    Err x   => verr x

||| Converts every value in a stream by applying a pure function.
export %inline
map : (a -> b) -> Pipe es es a b
map = listPipe . map

||| Replaces every value in a stream with the given replacement.
export %inline
const : b -> Pipe es es a b
const = map . const

||| Filter values in a stream according to the given predicate.
export %inline
filter : (a -> Bool) -> Pipe es es a a
filter = listPipe . filter

||| Converts values using the given function, keeping only results
||| wrapped in a `Just`.
export %inline
mapMaybe : (a -> Maybe b) -> Pipe es es a b
mapMaybe = listPipe . mapMaybe

||| Drop all `Nothing` values from a stream.
export %inline
catMaybes : Pipe es es (Maybe a) a
catMaybes = mapMaybe id

||| Convert values in a stream to strings by using their `Show` implementation.
export %inline
show : Show a => Pipe es es a String
show = map show

||| Like `show` but terminating every printed value with a line break.
export %inline
showLines : Show a => Pipe es es a String
showLines = map ((++ "\n") . show)

||| Ends every string in the stream with a line break.
export %inline
unlines : Pipe es es String String
unlines = map (++ "\n")

||| Converts strings to byte vectors.
export %inline
bytes : Pipe es es String ByteString
bytes = map fromString

||| Converts strings to byte vectors.
export %inline
string : Pipe es es ByteString String
string = map toString

--------------------------------------------------------------------------------
-- Error handling
--------------------------------------------------------------------------------

||| Error handling by converting errors to an IO action.
export
handle : (HSum es -> IO ()) -> Pipe es [] a a
handle f =
  syncPipe . pure $ \case
    Next vs => pure (vnext vs)
    Done vs => pure (vdone vs)
    Err  x  => f x $> vdone []

||| Silently drops any upstream error, converting an error message to
||| a `Done []`.
export
dropErrs : Pipe es [] a a
dropErrs = handle (const $ pure ())

--------------------------------------------------------------------------------
-- Mealy Machines
--------------------------------------------------------------------------------

||| A Mealy machine converts a message plus current state to a new
||| message and updated state.
export
mealyPipe : s -> ((m : Msg es a) -> s -> (s, ValidAfter m fs b)) -> Pipe es fs a b
mealyPipe ini f =
  syncPipe $ do
  st <- newIORef (Just ini)

  let fun : (m : Msg es a) -> IO (ValidAfter m fs b)
      fun m = do
        Just s1 <- readIORef st | Nothing => pure (vdone [])
        let (s2,m2) := f m s1
        if isTerminal (fst m2)
           then writeIORef st Nothing
           else writeIORef st (Just s2)
        pure m2

  pure fun

acc :
     SnocList b
  -> s
  -> (a -> s -> Maybe (s, b))
  -> List a
  -> (Maybe s, List b)
acc sx st f []        = (Just st, sx <>> [])
acc sx st f (x :: xs) =
  case f x st of
    Just (st2,vb) => acc (sx :< vb) st2 f xs
    Nothing       => (Nothing, sx <>> [])

||| Statefully accumulates values until the given function
||| returns `Nothing`.
export
accumTill : s -> (a -> s -> Maybe (s,b)) -> Pipe es es a b
accumTill  ini f =
  mealyPipe ini $ \m,s1 => case m of
    Next vs =>
      let (Just s2,vs) := acc [<] s1 f vs | (Nothing,vs) => (s1,vdone vs)
       in (s2,vnext vs)
    Done vs =>
      let (m,vs) := acc [<] s1 f vs
       in (fromMaybe s1 m,vdone vs)
    Err x => (s1,verr x)

||| Statefully accumulates values in a stream.
export %inline
accum : s -> (a -> s -> (s,b)) -> Pipe es es a b
accum s f = accumTill s (\x => Just . f x)

||| Keep only the first `n` values in a stream.
export %inline
take : (n : Nat) -> Pipe es es a a
take n = accumTill n (\v => \case 0 => Nothing; S k => Just (k, v))

||| Drop the first `n` values in a stream.
export %inline
drop : (n : Nat) -> Pipe es es a a
drop n =
  accum n (\v => \case 0 => (0, Just v); S k => (k, Nothing)) >>> catMaybes

||| Pairs every value in a stream with its corresponding index.
export %inline
zipWithIndex : Pipe es es a (Nat,a)
zipWithIndex = accum 0 (\v,k => (S k, (k,v)))

--------------------------------------------------------------------------------
-- Moore Machines
--------------------------------------------------------------------------------

||| A Moore machine computes the next value from the current value.
|||
||| Unlike a Mealy machine, a moore machine delays the generated output
||| by one iteration. This is useful for implementing delays, such as
||| when prepending values.
export
moorePipe : (List b -> List a -> List b) -> List b -> Pipe es es a b
moorePipe f ini =
  mealyPipe ini $ \m,bs =>
    case m of
      Next as => (f bs as, vnext bs)
      Done as => ([], vdone (bs ++ f bs as))
      Err x   => ([], verr x)

||| Prepends the given values to a stream of values.
export %inline
prepend : List a -> Pipe es es a a
prepend vs = moorePipe (const id) vs

||| Prepends the given value to a stream of values.
export %inline
cons : a -> Pipe es es a a
cons = prepend . pure

scanImpl : SnocList b -> (b -> a -> b) -> b -> List a -> (b,List b)
scanImpl sx f x []        = (x, sx <>> [])
scanImpl sx f x (y :: ys) = scanImpl (sx :< x) f (f x y) ys

||| Accumulates values using the given accumulator, starting with the
||| initial value.
|||
||| Like with `Data.Vect.scanl`, this will delay all values by one, and
||| - in case of a finite stream - increase the amount of emitted values
||| by one.
export
scan : (b -> a -> b) -> b -> Pipe es es a b
scan f ini =
  mealyPipe ini $ \m,b1 =>
    case m of
      Next x => let (b2,y) := scanImpl [<] f b1 x in (b2, vnext y)
      Done x => let (b2,y) := scanImpl [<] f b1 x in (b2, vdone $ y ++ [b2])
      Err x   => (b1, verr x)

--------------------------------------------------------------------------------
-- Splitting Byte Streams
--------------------------------------------------------------------------------

ls :  SnocList ByteString
   -> (n : Nat)
   -> ByteVect n
   -> (SnocList ByteString, ByteString)
ls sb n bs =
  case breakNL bs of
    MkBreakRes l1 0      b1 _  prf => (sb, BS l1 b1)
    MkBreakRes l1 (S l2) b1 b2 prf =>
      ls (sb :< BS l1 b1) (assert_smaller n l2) (tail b2)

lss :  SnocList ByteString
    -> ByteString
    -> List ByteString
    -> (List ByteString, ByteString)
lss sx x []          = (sx <>> [], x)
lss sx x (BS n bs :: bss) =
  case breakNL bs of
    MkBreakRes l1 0      b1 _  prf => lss sx (x <+> BS l1 b1) bss
    MkBreakRes l1 (S l2) b1 b2 prf =>
      let (sx2,x2) := ls (sx :< (x <+> BS l1 b1)) l2 (tail b2)
       in lss sx2 x2 bss

||| Splite a stream of byte strings into individual lines.
export
lines : Pipe es es ByteString ByteString
lines =
  mealyPipe ByteString.empty $ \m,s1 =>
    case m of
      Next vs => let (ws,s2) := lss [<] s1 vs in (s2,vnext ws)
      Done vs => let (ws,s2) := lss [<] s1 vs in (empty,vdone $ ws ++ [s2])
      Err x   => (s1,verr x)

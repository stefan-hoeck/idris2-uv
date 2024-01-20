module System.UV.Util

import Data.ByteString
import Data.ByteVect
import Data.IORef

%default total

public export
idris_uv : String -> String
idris_uv fn = "C:" ++ fn ++ ",libuv-idris"

export %inline
boolToInt32 : Bool -> Int32
boolToInt32 False = 0
boolToInt32 True  = 1

export %inline
int32ToBool : Int32 -> Bool
int32ToBool 0 = False
int32ToBool _ = True

--------------------------------------------------------------------------------
-- Accumulating Lines: TODO: This should probably go to idris2-bytestring
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

export %inline
accumLines : (rem, next : ByteString) -> (List ByteString, ByteString)
accumLines rem bs = lss [<] rem [bs]

export %inline
accumLinesN :
     (rem : ByteString)
  -> List ByteString
  -> (List ByteString, ByteString)
accumLinesN = lss [<]

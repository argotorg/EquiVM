import Std.Data.HashMap
import Solm.Value.Basic
import Solm.Value.DecEq

namespace Solm

def valueToWord : Value -> Option EVM.Word
  | .int i => pure $ EVM.wordOfInt i
  | .unit => .none
  | .bool b => b.toUInt256
  | .address a => pure $ .ofNat $ a.toNat
  | .array _ => .none
  | .tuple _ => .none
  | .struct _ _ => .none
  | .bytes _ => .none
  | .fixedBytes n bs =>
      if bs.length = n.val + 1 then
        some (.ofNat (Ethereum.fromBytesBigEndian bs))
      else
        none
  | .storageRef _ _ => .none

def wordToElem (t : ABI.ElemType) (w : EVM.Word) : Value :=
  match t with
  | .int (.uint _) => .int (w.toNat)
  | .int (.sint bits) =>
      -- Sign-extend at the *declared* width, as solc's `SIGNEXTEND` on load.  The leading mask
      -- (`% 2^bits`) is load-bearing: under a nonzero `bitOffset` `storageLocLoad` shift-rights the
      -- slot word, so bits above the field can hold packed neighbours — the mask drops them.  For
      -- `bits = 256` this coincides with `EVM.signed` (see the `#guard` below).
      let m := w.toNat % EVM.twoPow bits.val
      .int (if m < EVM.twoPow (bits.val - 1) then (m : Int)
        else (m : Int) - (EVM.twoPow bits.val : Int))
  | .bool => if w.val == 0 then .bool false else .bool true
  | .address => .address (.ofNat $ w.toNat)
  | .bytes n => .fixedBytes n (w.toBytesBE.drop (32 - (n.val + 1)))
  -- TODO: implement
  | .function => panic! "TODO: wordToElem: implement function"
  | .fixed _ => panic! "TODO: wordToElem: implement fixed"

-- Packed signed loads sign-extend at the declared width; unsigned loads are unchanged; and at the
-- full width the signed arm still agrees with `EVM.signed` (here: `2^255 ↦ -2^255`).
#guard wordToElem (.int (.sint ⟨24, by decide⟩)) (EVM.Word.ofNat 0xFFFFFF) = .int (-1)
#guard wordToElem (.int (.sint ⟨24, by decide⟩)) (EVM.Word.ofNat 0x7FFFFF) = .int 8388607
#guard wordToElem (.int (.uint ⟨24, by decide⟩)) (EVM.Word.ofNat 0xFFFFFF) = .int 16777215
#guard wordToElem (.int (.sint ⟨256, by decide⟩)) (EVM.Word.ofNat (EVM.twoPow 255))
  = .int (EVM.signed (EVM.Word.ofNat (EVM.twoPow 255)))
#guard wordToElem (.int (.sint ⟨256, by decide⟩)) (EVM.Word.ofNat (EVM.twoPow 255))
  = .int (-(EVM.twoPow 255 : Int))

abbrev Store := Std.HashMap Ident Value

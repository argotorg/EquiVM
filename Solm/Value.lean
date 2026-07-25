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

def keyValueToWord : KeyValue -> EVM.Word
  | .int i => EVM.wordOfInt i
  | .bool b => b.toUInt256
  | .address a =>
    { val := (@Fin.castLE Ethereum.AccountAddress.size
                          Ethereum.UInt256.size
                            (by unfold Ethereum.AccountAddress.size Ethereum.UInt256.size; simp) a : Fin Ethereum.UInt256.size) }
  | .fixedBytes n bs =>
      -- `bytesN` keys are LEFT-aligned in the hashed word: `value * 2^(8·(31-n))` (solc 0.6.12 &
      -- 0.8.35 mask the key to its high bytes before `keccak256`).  `bytes32` (`n=31`) is `×1`.
      if bs.length = n.val + 1 then
        EVM.Word.ofNat (Ethereum.fromBytesBigEndian bs * 2 ^ (8 * (31 - n.val)))
      else
        -- Unreachable on the eval path (`valueToKey?` rejects length-mismatched keys); total fallback.
        ⟨0⟩
#guard keyValueToWord (.fixedBytes ⟨3, by decide⟩ [0xDE, 0xAD, 0xBE, 0xEF])
  = EVM.Word.ofNat (0xDEADBEEF * 2 ^ 224)
#guard keyValueToWord (.fixedBytes ⟨31, by decide⟩ (List.replicate 31 0 ++ [0x2A]))
  = EVM.Word.ofNat 0x2A

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

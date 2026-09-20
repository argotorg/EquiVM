import Std.Data.HashMap
import ABI.Value
import Solm.Value.Basic
import Solm.Value.DecEq

namespace Solm

open ABI

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

mutual
/-- Sol⁻ values from ABI values.  The decoder's raw `bool` word becomes Sol⁻'s marker
    `.tuple [.unit, .int n]`, validated on access (`normalizeRawBoolWord?`). -/
@[reducible, simp] def Value.ofABI : ABIValue → Value
  | .int i => .int i
  | .bool b => .bool b
  | .address a => .address a
  | .fixedBytes n bs => .fixedBytes n bs
  | .bytes ba => .bytes ba
  | .array vs => .array (Value.ofABIList vs)
  | .tuple vs => .tuple (Value.ofABIList vs)
  | .rawBool n => .tuple [.unit, .int n]

@[reducible, simp] def Value.ofABIList : List ABIValue → List Value
  | [] => []
  | v :: vs => Value.ofABI v :: Value.ofABIList vs
end

mutual
/-- ABI values from Sol⁻ values; `none` for what the ABI cannot carry (structs, storage
    references, `unit`). -/
@[reducible, simp] def Value.toABI? : Value → Option ABIValue
  | .int i => some (.int i)
  | .bool b => some (.bool b)
  | .address a => some (.address a)
  | .fixedBytes n bs => some (.fixedBytes n bs)
  | .bytes ba => some (.bytes ba)
  | .array vs => (Value.toABIList? vs).map .array
  | .tuple vs => (Value.toABIList? vs).map .tuple
  | .struct _ _ | .storageRef _ _ | .unit => none

@[reducible, simp] def Value.toABIList? : List Value → Option (List ABIValue)
  | [] => some []
  | v :: vs => do
      let a ← Value.toABI? v
      let as ← Value.toABIList? vs
      some (a :: as)
end

abbrev Store := Std.HashMap Ident Value

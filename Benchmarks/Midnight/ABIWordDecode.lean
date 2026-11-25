import Benchmarks.Midnight.MarketDecode

/-! Word-at-a-time views of scalar fields in the modern ABI decoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem readWord_bytes {bytes : ByteArray} {off : Nat} (h : off + 32 ≤ bytes.size) :
    readWord? bytes.toList off = some (calldataWord bytes off) := by
  have hlen : ((bytes.toList.drop off).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
    change min 32 (bytes.size - off) = 32
    omega
  simp only [readWord?, readBytes?, hlen, if_true, bind, Option.bind,
    decode_word_at_eq_any bytes off h]

theorem decodeABIWord_u256 (word : UInt256) :
    decodeABIWord? Model.u256 word = some (.int (Int.ofNat word.toNat)) := by
  have hb : word.val.val < EVM.twoPow 256 := word.val.isLt
  simp only [Model.u256, decodeABIWord?, show ¬ (256 : Nat) = 0 by decide, if_false,
    hb, if_true]
  rfl

theorem decodeABIWord_address (word : UInt256) :
    decodeABIWord? Model.addr word =
      if word.toNat < EVM.addressModulus then
        some (.address (AccountAddress.ofNat word.toNat)) else none := rfl

-- LIBRARY CANDIDATE: separate a scalar field's input bounds from word validation.
theorem decodeABIValue_word {ty : ABIType} {bytes : ByteArray} {start : Nat}
    (hty : isABIScalarWordType ty = true) (hlen : start + 32 ≤ bytes.size) :
    decodeABIValue? ty bytes.toList start =
      (decodeABIWord? ty (calldataWord bytes start)).map (fun value ↦ (value, start + 32)) := by
  rw [decodeABIValue_scalarWord_eq hty]
  simp only [decodeScalarWord?, readWord_bytes hlen, bind, Option.bind]
  cases decodeABIWord? ty (calldataWord bytes start) <;> rfl

-- LIBRARY CANDIDATE: one scalar tuple head advances the cursor by one word.
theorem decodeABIValues_word {ty : ABIType} {types : List ABIType} {bytes : ByteArray}
    {base cursor headSize maxEnd : Nat}
    (hty : isABIScalarWordType ty = true) (hlen : base + cursor + 32 ≤ bytes.size) :
    decodeABIValues? (ty :: types) bytes.toList base cursor headSize maxEnd = (do
      let value ← decodeABIWord? ty (calldataWord bytes (base + cursor))
      let rest ← decodeABIValues? types bytes.toList base (cursor + 32) headSize
        (max maxEnd (base + cursor + 32))
      pure (value :: rest.1, rest.2)) := by
  rw [decodeABIValues?]
  simp only [isABIScalarWordType_dynamic hty, Bool.false_eq_true, if_false,
    isABIScalarWordType_size hty, bind, Option.bind, decodeABIValue_word hty hlen]
  cases decodeABIWord? ty (calldataWord bytes (base + cursor)) <;>
    simp only [Option.map, if_true] <;> rfl

end Benchmarks.Midnight

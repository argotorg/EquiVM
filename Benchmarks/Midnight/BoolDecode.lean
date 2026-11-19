import Benchmarks.Midnight.PairDecode

/-! Boolean calldata words and the compiler's canonicality check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: canonical boolean decoding expressed by the two EVM words.
theorem decodeABIWord_bool (word : UInt256) :
    decodeABIWord? (.elem .bool) word =
      if word = ⟨0⟩ ∨ word = ⟨1⟩ then some (wordToElem .bool word) else none := by
  by_cases hz : word = ⟨0⟩
  · subst word
    rfl
  by_cases ho : word = ⟨1⟩
  · subst word
    rfl
  have hnz : word.toNat ≠ 0 := fun h ↦ hz (u256_inj h)
  have hno : word.toNat ≠ 1 := fun h ↦ ho (u256_inj h)
  change (if word.toNat = 0 then _ else if word.toNat = 1 then _ else _) = _
  simp only [hz, ho, hnz, hno, false_or, if_false]

-- LIBRARY CANDIDATE: decode a canonical boolean at any calldata offset.
theorem decodeBoolWord {cd : ByteArray} {off : Nat} (hlen : off + 32 ≤ cd.size)
    (hbool : calldataWord cd off = ⟨0⟩ ∨ calldataWord cd off = ⟨1⟩) :
    decodeABIValue? (.elem .bool) ((cd.toList.drop off).take 32) 0 =
      some (wordToElem .bool (calldataWord cd off), 32) := by
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have ht : ((((cd.toList.drop off).take 32).drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.take_take, Nat.min_self, List.length_take,
      List.length_drop, hlist]; omega
  have hw : ABI.bytesToWord ((((cd.toList.drop off).take 32).drop 0).take 32) =
      calldataWord cd off := by
    simpa only [List.drop_zero, List.take_take, Nat.min_self] using decode_word_at_eq_any cd off hlen
  rw [decodeABIValue_scalarWord_eq (by decide)]
  rcases hbool with hz | ho
  · rw [decodeScalarWord_bool_ok_zero ht (hw.trans hz), hz]; rfl
  · rw [decodeScalarWord_bool_ok_one ht (hw.trans ho), ho]; rfl

theorem decodeBoolWord_none {cd : ByteArray} {off : Nat} (hlen : off + 32 ≤ cd.size)
    (hbool : ¬ (calldataWord cd off = ⟨0⟩ ∨ calldataWord cd off = ⟨1⟩)) :
    decodeABIValue? (.elem .bool) ((cd.toList.drop off).take 32) 0 = none := by
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeABIValue_scalarWord_eq (by decide)]
  apply decodeScalarWord_bool_none_noncanon
  · simp only [List.drop_zero, List.take_take, Nat.min_self, List.length_take,
      List.length_drop, hlist]; omega
  · simpa only [List.drop_zero, List.take_take, Nat.min_self, decode_word_at_eq_any cd off hlen]
      using fun hz ↦ hbool (Or.inl hz)
  · simpa only [List.drop_zero, List.take_take, Nat.min_self, decode_word_at_eq_any cd off hlen]
      using fun ho ↦ hbool (Or.inr ho)

end Benchmarks.Midnight

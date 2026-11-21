import Benchmarks.Midnight.PairDecode

/-! Canonical unsigned scalar calldata words of arbitrary ABI width. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES Reasoning.Theory.decodeScalarWord_uint_result to calldata slices.
theorem decodeUintWord_result {cd : ByteArray} {off : Nat} (bits : BitWidth)
    (hlen : off + 32 ≤ cd.size) :
    decodeABIValue? (.elem (.int (.uint bits))) ((cd.toList.drop off).take 32) 0 =
      if (calldataWord cd off).toNat < EVM.twoPow bits.val then
        some (.int (Int.ofNat (calldataWord cd off).toNat), 32) else none := by
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeABIValue_scalarWord_eq (by rfl), decodeScalarWord_uint_result bits (by
    simp only [List.drop_zero, List.take_take, Nat.min_self, List.length_take,
      List.length_drop, hlist]; omega)]
  simp only [List.drop_zero, List.take_take, Nat.min_self, decode_word_at_eq_any cd off hlen]

theorem decodeUintWord {cd : ByteArray} {off : Nat} (bits : BitWidth)
    (hlen : off + 32 ≤ cd.size) (hcanon : (calldataWord cd off).toNat < EVM.twoPow bits.val) :
    decodeABIValue? (.elem (.int (.uint bits))) ((cd.toList.drop off).take 32) 0 =
      some (.int (Int.ofNat (calldataWord cd off).toNat), 32) := by
  rw [decodeUintWord_result bits hlen, if_pos hcanon]

theorem decodeUintWord_none {cd : ByteArray} {off : Nat} (bits : BitWidth)
    (hlen : off + 32 ≤ cd.size) (hcanon : ¬ (calldataWord cd off).toNat < EVM.twoPow bits.val) :
    decodeABIValue? (.elem (.int (.uint bits))) ((cd.toList.drop off).take 32) 0 = none := by
  rw [decodeUintWord_result bits hlen, if_neg hcanon]

end Benchmarks.Midnight

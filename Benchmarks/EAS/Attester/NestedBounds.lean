import Benchmarks.EAS.Attester.NestedDecodeTrace
import Benchmarks.EAS.Attester.ArrayBounds
import Benchmarks.EAS.Attester.WordHelpers

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Theory

-- LIBRARY CANDIDATE: CALLDATALOAD returns zero beyond the calldata buffer, at any word address.
theorem calldataWord_zero_of_ge {cd : ByteArray} {off : Nat} (h : cd.size ≤ off) :
    calldataWord cd off = ⟨0⟩ := by
  have hcopy : cd.copySlice off ByteArray.empty 0 32 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_copySlice]
    simp only [ByteArray.data_empty, Array.extract_empty, Array.empty_append,
      Array.append_empty, Nat.zero_add]
    exact Array.extract_eq_empty_of_le (by change min (off + 32) cd.size ≤ off; omega)
  have hdrop : cd.toList.drop off = [] := by
    apply List.drop_eq_nil_of_le
    simpa only [byteArray_toList_eq, Array.length_toList] using h
  have hread : cd.readBytes off 32 = ByteArray.zeroes 32 := by
    unfold ByteArray.readBytes
    split_ifs <;> simp only [hcopy, hdrop, List.take_nil,
      show (ByteArray.empty).size = 0 from rfl, Nat.sub_zero, ByteArray.empty_append] <;> rfl
  change uInt256OfByteArray (cd.readBytes off 32) = _
  rw [hread]
  native_decide

-- LIBRARY CANDIDATE: a nonnegative left operand bounds both the sign and value on the right.
theorem sgt_zero_of_left_low {a b : UInt256} (ha : a.toNat < 2 ^ 255)
    (h : UInt256.sgt a b = ⟨0⟩) : b.toNat < 2 ^ 255 ∧ a.toNat ≤ b.toNat := by
  by_cases hb : 2 ^ 255 ≤ b.toNat
  · simp only [UInt256.sgt, UInt256.sgtBool, if_neg (by omega : ¬ 2 ^ 255 ≤ a.toNat),
      if_pos hb] at h
    contradiction
  refine ⟨by omega, ?_⟩
  by_contra hgt
  have hgt' : a > b := by change a.toNat > b.toNat; omega
  simp only [UInt256.sgt, UInt256.sgtBool, if_neg (by omega : ¬ 2 ^ 255 ≤ a.toNat),
    if_neg hb, decide_eq_true hgt'] at h
  contradiction

-- LIBRARY CANDIDATE: signed comparison agrees with unsigned comparison for nonnegative words.
theorem sgt_zero_low {a b : UInt256} (ha : a.toNat < 2 ^ 255) (hb : b.toNat < 2 ^ 255)
    (hab : a.toNat ≤ b.toNat) : UInt256.sgt a b = ⟨0⟩ := by
  have hnot : ¬ a > b := by change ¬ a.toNat > b.toNat; omega
  simp only [UInt256.sgt, UInt256.sgtBool, if_neg (by omega : ¬ 2 ^ 255 ≤ a.toNat),
    if_neg (by omega : ¬ 2 ^ 255 ≤ b.toNat), decide_eq_false hnot]
  rfl

-- LIBRARY CANDIDATE: the signed limit used by solc's nested-array header guard.
theorem nestedHeaderLimit {size : Nat} {base : UInt256}
    (hs : size < 2 ^ 255) (hb : base.toNat + 32 ≤ size) :
    UInt256.sub (UInt256.ofNat size) base + UInt256.ofNat (UInt256.size - 31) =
      UInt256.ofNat (size - base.toNat - 31) := by
  apply u256_inj
  rw [uadd_toNat, usub_ofNat_word_toNat (by omega) (lt_size_of_lt_sign hs),
    ulit_toNat' (size - base.toNat - 31) (by have := lt_size_of_lt_sign hs; omega)]
  have hneg : (UInt256.ofNat (UInt256.size - 31)).toNat = 2 ^ 256 - 31 := by native_decide
  rw [hneg]
  rw [show UInt256.size = 2 ^ 256 by norm_num [UInt256.size]]
  omega

-- LIBRARY CANDIDATE: wrapped relative addresses obey the nested-array signed header guard.
theorem nestedHeader_of_bound {size : Nat} {base relative : UInt256}
    (hs : size < 2 ^ 255) (hb : base.toNat + 32 ≤ size)
    (ht : (base + relative).toNat + 32 ≤ size) :
    UInt256.slt relative
      (UInt256.sub (UInt256.ofNat size) base + UInt256.ofNat (UInt256.size - 31)) ≠ ⟨0⟩ := by
  rw [nestedHeaderLimit hs hb]
  by_cases hr : relative.toNat < 2 ^ 255
  · have hsum := uadd_toNat base relative
    change (base + relative).toNat = (base.toNat + relative.toNat) % (2 ^ 256) at hsum
    rw [slt_lit_one_low (by omega) (by omega)]
    decide
  · rw [slt_lit_one_high (by omega) (by omega)]
    decide

-- LIBRARY CANDIDATE: a nonzero, readable target turns the signed header guard into a byte bound.
theorem nestedHeader_to_bound {size : Nat} {base relative : UInt256}
    (hs : size < 2 ^ 255) (hb : base.toNat + 32 ≤ size)
    (ht : (base + relative).toNat < size)
    (h : UInt256.slt relative
      (UInt256.sub (UInt256.ofNat size) base + UInt256.ofNat (UInt256.size - 31)) ≠ ⟨0⟩) :
    (base + relative).toNat + 32 ≤ size := by
  rw [nestedHeaderLimit hs hb] at h
  have hsum := uadd_toNat base relative
  change (base + relative).toNat = (base.toNat + relative.toNat) % (2 ^ 256) at hsum
  have hrfit : relative.toNat < 2 ^ 256 := relative.val.isLt
  by_cases hr : relative.toNat < 2 ^ 255
  · have hrbound : relative.toNat < size - base.toNat - 31 := by
      by_contra hbad
      exact h (slt_lit_zero (by omega) (by omega) hr)
    omega
  · omega

-- LIBRARY CANDIDATE: the signed payload check for a nested array of EVM words.
theorem nestedPayload_of_bound {size : Nat} {head len : UInt256}
    (hs : size < 2 ^ 255) (hlen : len.toNat ≤ solcMaxU64)
    (hb : head.toNat + 32 + 32 * len.toNat ≤ size) :
    UInt256.isZero (UInt256.sgt (UInt256.ofNat 32 + head)
      (UInt256.sub (UInt256.ofNat size) (UInt256.shiftLeft len (UInt256.ofNat 5)))) ≠ ⟨0⟩ := by
  have hm : 32 * len.toNat < UInt256.size := by have := lt_size_of_lt_sign hs; omega
  have hshift : UInt256.shiftLeft len (UInt256.ofNat 5) = UInt256.ofNat (32 * len.toNat) := by
    conv_lhs => rw [← u256_ofNat_toNat len]
    exact shiftLeft5_ofNat_eq hm
  have hdata : (UInt256.ofNat 32 + head).toNat = head.toNat + 32 :=
    uadd_lit32_toNat head (by have := lt_size_of_lt_sign hs; omega)
  rw [hshift, ofNat_sub_words (by omega) (lt_size_of_lt_sign hs)]
  have hright := ulit_toNat' (size - 32 * len.toNat) (by have := lt_size_of_lt_sign hs; omega)
  rw [sgt_zero_low (by rw [hdata]; omega) (by rw [hright]; omega)
    (by rw [hdata, hright]; omega)]
  decide

theorem nestedPayload_to_bound {size : Nat} {head len : UInt256}
    (hs : size < 2 ^ 255) (hlen : len.toNat ≤ solcMaxU64) (hh : head.toNat + 32 ≤ size)
    (h : UInt256.isZero (UInt256.sgt (UInt256.ofNat 32 + head)
      (UInt256.sub (UInt256.ofNat size) (UInt256.shiftLeft len (UInt256.ofNat 5)))) ≠ ⟨0⟩) :
    head.toNat + 32 + 32 * len.toNat ≤ size := by
  have hmlo : 32 * len.toNat < 2 ^ 255 := by
    change len.toNat ≤ 18446744073709551615 at hlen
    omega
  have hm := lt_size_of_lt_sign hmlo
  have hshift : UInt256.shiftLeft len (UInt256.ofNat 5) = UInt256.ofNat (32 * len.toNat) := by
    conv_lhs => rw [← u256_ofNat_toNat len]
    exact shiftLeft5_ofNat_eq hm
  have hdata : (UInt256.ofNat 32 + head).toNat = head.toNat + 32 :=
    uadd_lit32_toNat head (by have := lt_size_of_lt_sign hs; omega)
  rw [hshift] at h
  have hright := sgt_zero_of_left_low (by rw [hdata]; omega) (u256_isZero_ne_zero_to_eq_zero h)
  have hsize := ulit_toNat' size (lt_size_of_lt_sign hs)
  have hmul := ulit_toNat' (32 * len.toNat) hm
  by_cases hsub : 32 * len.toNat ≤ size
  · rw [usub_toNat (by rw [hsize, hmul]; exact hsub), hsize, hmul, hdata] at hright
    omega
  · rw [usub_toNat_underflow (by rw [hsize, hmul]; omega), hsize, hmul] at hright
    have hw : UInt256.size = 2 ^ 256 := by norm_num [UInt256.size]
    rw [hw] at hright
    omega

end Reasoning.Theory

namespace Benchmarks.EAS.Attester

theorem NestedHeadChecks.of_bounds {cd : ByteArray} {base entry : UInt256}
    (hs : cd.size < 2 ^ 255) (hb : base.toNat + 32 ≤ cd.size)
    (hlen : (calldataWord cd (nestedHead cd base entry).toNat).toNat ≤ solcMaxU64)
    (ht : (nestedHead cd base entry).toNat + 32 +
      32 * (calldataWord cd (nestedHead cd base entry).toNat).toNat ≤ cd.size) :
    NestedHeadChecks cd base entry :=
  ⟨nestedHeader_of_bound hs hb
      (by change (nestedHead cd base entry).toNat + 32 ≤ cd.size; omega),
    by rw [ugt_zero hlen]; decide,
    nestedPayload_of_bound hs hlen ht⟩

theorem NestedHeadChecks.bounds {cd : ByteArray} {base entry : UInt256}
    (h : NestedHeadChecks cd base entry)
    (hs : cd.size < 2 ^ 255) (hb : base.toNat + 32 ≤ cd.size)
    (hne : calldataWord cd (nestedHead cd base entry).toNat ≠ ⟨0⟩) :
    (nestedHead cd base entry).toNat + 32 +
      32 * (calldataWord cd (nestedHead cd base entry).toNat).toNat ≤ cd.size := by
  have ht : (nestedHead cd base entry).toNat < cd.size := by
    by_contra hbad
    exact hne (calldataWord_zero_of_ge (by omega))
  have hheader := nestedHeader_to_bound hs hb ht h.header
  exact nestedPayload_to_bound hs (uint64Bound_of_isZero_gt h.length) hheader h.payload

def RowValid (cd : ByteArray) (base : UInt256) (i : Nat) : Prop :=
  NestedHeadChecks cd base (rowEntry base i) ∧ rowLength cd base i ≠ ⟨0⟩

theorem RowValid.bounds {cd : ByteArray} {base : UInt256} {i : Nat}
    (h : RowValid cd base i) (hs : cd.size < 2 ^ 255) (hb : base.toNat + 32 ≤ cd.size) :
    0 < (rowLength cd base i).toNat ∧ (rowLength cd base i).toNat ≤ solcMaxU64 ∧
      (rowData cd base i).toNat + 32 * (rowLength cd base i).toNat ≤ cd.size := by
  have hh := h.1.bounds hs hb h.2
  change (rowHead cd base i).toNat + 32 + 32 * (rowLength cd base i).toNat ≤ cd.size at hh
  have hn : (rowLength cd base i).toNat ≠ 0 := by
    intro heq
    apply h.2
    apply u256_inj
    exact heq
  refine ⟨by omega, uint64Bound_of_isZero_gt h.1.length, ?_⟩
  have hdata : (UInt256.ofNat 32 + rowHead cd base i).toNat = (rowHead cd base i).toNat + 32 :=
    uadd_lit32_toNat _ (by have := lt_size_of_lt_sign hs; omega)
  rw [rowData, hdata]
  exact hh

end Benchmarks.EAS.Attester

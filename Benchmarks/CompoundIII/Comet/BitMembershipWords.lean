import Benchmarks.CompoundIII.Comet.IsInAssetModel
import Benchmarks.CompoundIII.Comet.BoolWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: double ISZERO canonicalizes a word's nonzero predicate.
theorem wordBooleanNonzero (w : UInt256) :
    UInt256.isZero (UInt256.isZero w) = boolWord (decide (w.toNat ≠ 0)) := by
  by_cases hz : w = ⟨0⟩
  · subst w
    decide
  · have hn : w.toNat ≠ 0 := fun h ↦ hz (uint256_toNat_eq_zero h)
    rw [isZero_eq_zero_of_ne hz]
    simp only [decide_eq_true hn, boolWord, if_true]
    rfl

-- LIBRARY CANDIDATE: a masked EVM bit test agrees with the source bit-membership predicate.
theorem bitMembership_word (value bit mask : UInt256) (width : Nat)
    (hv : value.toNat < 2^width) (hb : bit.toNat < 256)
    (hm : mask.toNat = 2^width - 1) :
    UInt256.isZero (UInt256.isZero
      (UInt256.land (UInt256.land (UInt256.shiftLeft (UInt256.ofNat 1) bit) value) mask)) =
      boolWord (bitMembership value bit.toNat) := by
  have hbits : (UInt256.land (UInt256.shiftLeft (UInt256.ofNat 1) bit) value).toNat <
      2^width := by
    rw [uland_toNat]
    exact lt_of_le_of_lt (nat_land_le_right _ _) hv
  rw [u256LandMaskCleanOfToNat _ _ hm hbits, wordBooleanNonzero, wordBitMask bit hb]
  unfold bitMembership
  rw [uland_toNat, UInt256.toNat_ofNat_of_lt
    (show 2^bit.toNat < UInt256.size from Nat.pow_lt_pow_right (by decide) hb), Nat.land_comm]
  rfl

-- LIBRARY CANDIDATE: subtracting sixteen using the compiler's complement-and-add encoding.
theorem wordComplement15Add (offset : UInt256) :
    UInt256.lnot (UInt256.ofNat 15) + offset = UInt256.sub offset (UInt256.ofNat 16) := by
  apply u256_inj
  have hb (x : BitVec 256) : (~~~(15 : BitVec 256)) + x = x - 16 := by bv_decide
  exact congrArg BitVec.toNat (hb ⟨offset.val⟩)

theorem isInAssetOffset_word (offset : UInt256) (hlo : 16 ≤ offset.toNat)
    (hhi : offset.toNat < 24) :
    UInt256.land (UInt256.lnot (UInt256.ofNat 15) + offset) (UInt256.ofNat 255) =
      UInt256.ofNat (offset.toNat - 16) := by
  rw [wordComplement15Add]
  have hsub : (UInt256.sub offset (UInt256.ofNat 16)).toNat = offset.toNat - 16 :=
    usub_toNat hlo
  rw [u256LandMaskCleanOfToNat _ _ (bits := 8) rfl (by
    change (UInt256.sub offset (UInt256.ofNat 16)).toNat < 256
    rw [hsub]
    omega)]
  apply u256_inj
  rw [hsub, UInt256.toNat_ofNat_of_lt (by change offset.toNat - 16 < 2^256; omega)]

end Benchmarks.CompoundIII.Comet

import Benchmarks.UniswapV3.Pool.PackedFieldWord
import Benchmarks.UniswapV3.Pool.SourceSignedBits

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: a shifted packed field is contained in its field mask.
theorem packedFieldValue_mask (value : UInt256) (offset width : Nat)
    (hoff : offset < 256) (hb : width + offset < 256) :
    UInt256.land (packedFieldValue value offset width)
      (UInt256.ofNat ((2 ^ width - 1) * 2 ^ offset)) = packedFieldValue value offset width := by
  have hc : (UInt256.land value (UInt256.ofNat (2 ^ width - 1))).toNat < 2 ^ width :=
    u256LandMaskToNatLtOfToNat (bits := width) _ _ (UInt256.toNat_ofNat_of_lt
      (lt_of_lt_of_le (Nat.sub_lt (by positivity) (by decide))
        (Nat.pow_le_pow_right (by decide) (by omega : width ≤ 256))))
  unfold packedFieldValue
  rw [← wordShiftLeft_eq_mul _ offset hoff]
  exact shiftLeft_land_mask _ width offset hoff hb hc

-- LIBRARY CANDIDATE: a larger mask preserves a word already preserved by a smaller mask.
theorem wordMask_preserves_of_contains (word mask keep : UInt256)
    (hw : UInt256.land word mask = word) (hm : UInt256.land mask keep = mask) :
    UInt256.land word keep = word := by
  have hw' := congrArg UInt256.toNat hw
  have hm' := congrArg UInt256.toNat hm
  simp only [uland_toNat] at hw' hm'
  apply u256_inj
  rw [uland_toNat]
  calc
    word.toNat &&& keep.toNat = (word.toNat &&& mask.toNat) &&& keep.toNat := by rw [hw']
    _ = word.toNat &&& (mask.toNat &&& keep.toNat) := Nat.and_assoc _ _ _
    _ = word.toNat := by rw [hm', hw']

-- LIBRARY CANDIDATE: packed writes commute when each clear mask preserves the other field.
theorem wordMaskedUpdate_comm (old left right leftMask rightMask : UInt256)
    (hl : UInt256.land left rightMask = left) (hr : UInt256.land right leftMask = right) :
    UInt256.lor (UInt256.land (UInt256.lor (UInt256.land old leftMask) left) rightMask) right =
      UInt256.lor (UInt256.land (UInt256.lor (UInt256.land old rightMask) right) leftMask) left := by
  have hl' := congrArg UInt256.toNat hl
  have hr' := congrArg UInt256.toNat hr
  simp only [uland_toNat] at hl' hr'
  apply u256_inj
  simp only [u256_lor_toNat_exact, uland_toNat, Nat.and_or_distrib_right, hl', hr']
  rw [Nat.and_right_comm old.toNat leftMask.toNat rightMask.toNat, Nat.or_right_comm]

end Benchmarks.UniswapV3.Pool

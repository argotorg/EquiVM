import Benchmarks.UniswapV3.Pool.WordShiftBits

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: the retained low bits determine a wrapping left shift.
theorem wordShiftLeft_residue (w bits : UInt256) (hbits : bits.toNat < 256) :
    (UInt256.shiftLeft w bits).toNat =
      (w.toNat % 2 ^ (256 - bits.toNat)) * 2 ^ bits.toNat := by
  rw [wordShiftLeft_toNat _ _ hbits]
  have hp : UInt256.size = 2 ^ (256 - bits.toNat) * 2 ^ bits.toNat := by
    rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hbits)]
    rfl
  rw [hp, Nat.mul_mod_mul_right]

-- LIBRARY CANDIDATE: a left shift already has all the cleared low bits set to zero.
theorem wordShiftLeft_highMask (w bits mask : UInt256) (hbits : bits.toNat < 256)
    (hmask : mask.toNat = 2 ^ 256 - 2 ^ bits.toNat) :
    UInt256.land (UInt256.shiftLeft w bits) mask = UInt256.shiftLeft w bits := by
  apply u256_inj
  rw [uland_toNat, hmask]
  change Nat.land (UInt256.shiftLeft w bits).toNat (2 ^ 256 - 2 ^ bits.toNat) = _
  rw [natLandClearLow (UInt256.shiftLeft w bits).toNat bits.toNat (Nat.le_of_lt hbits)
      (UInt256.shiftLeft w bits).val.isLt,
    wordShiftLeft_residue _ _ hbits, Nat.mul_div_cancel _ (by positivity)]

-- LIBRARY CANDIDATE: equal left/right shifts implement truncation to the retained field.
theorem wordShiftLeftRight_mask (w bits mask : UInt256) (hbits : bits.toNat < 256)
    (hmask : mask.toNat = 2 ^ (256 - bits.toNat) - 1) :
    UInt256.shiftRight (UInt256.shiftLeft w bits) bits = UInt256.land w mask := by
  apply u256_inj
  rw [wordShiftRight_toNat _ _ hbits, wordShiftLeft_residue _ _ hbits,
    Nat.mul_div_cancel _ (by positivity), uland_toNat, hmask]
  exact (nat_land_mask_eq_mod _ _).symm

end Benchmarks.UniswapV3.Pool

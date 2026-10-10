import Benchmarks.CompoundIII.Comet.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: unsigned casts truncate an EVM word to an arbitrary Solidity width.
def uintCastWord (width : BitWidth) (word : UInt256) : UInt256 :=
  UInt256.land word (UInt256.ofNat (2^width.val - 1))

theorem uintCastWord_mask (width : BitWidth) :
    (UInt256.ofNat (2^width.val - 1)).toNat = 2^width.val - 1 := by
  apply UInt256.toNat_ofNat_of_lt
  have hp : 2^width.val ≤ UInt256.size := by
    change 2^width.val ≤ 2^256
    exact Nat.pow_le_pow_right (by decide) width.property.2.1
  have hpos : 0 < 2^width.val := by positivity
  omega

theorem uintCastWord_lt (width : BitWidth) (word : UInt256) :
    (uintCastWord width word).toNat < 2^width.val :=
  u256LandMaskToNatLtOfToNat word _ (uintCastWord_mask width)

theorem uintCastWord_nat (width : BitWidth) (word : UInt256) :
    (uintCastWord width word).toNat = word.toNat % 2^width.val := by
  rw [uintCastWord, uland_toNat, uintCastWord_mask]
  change Nat.land word.toNat (2^width.val - 1) = word.toNat % 2^width.val
  rw [nat_land_mask_eq_mod]

theorem uintCastWord_source {cfg frame evm expr word} (width : BitWidth)
    (he : evalExpr? cfg frame evm expr = .ok (.int (Int.ofNat word.toNat))) :
    evalExpr? cfg frame evm (.cast expr (.elem (.int (.uint width)))) =
      .ok (.int (uintCastWord width word).toNat) := by
  have hc := evalExpr_cast_int (intType := .uint width) he
  rw [uintCastWord_nat]
  simpa only [normalizeInt, EVM.twoPow, Int.ofNat_eq_natCast, Int.natCast_emod] using hc

end Benchmarks.CompoundIII.Comet

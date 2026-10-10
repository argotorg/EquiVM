import Benchmarks.UniswapV3.Pool.AmountDeltaSortTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem amount0DeltaNumeratorMask (a : AmountDeltaArgs) (hfit : a.Fits) :
    UInt256.land (UInt256.shiftLeft a.liquidity (UInt256.ofNat 96))
      (UInt256.ofNat 26959946667150639794667015087019630673557916260026308143510066298880) =
      amountDeltaNumerator a := by
  have hmask : UInt256.ofNat
      26959946667150639794667015087019630673557916260026308143510066298880 =
      UInt256.land (UInt256.ofNat (2 ^ 224 - 1))
        (UInt256.ofNat (2 ^ 256 - 2 ^ 96)) := by native_decide
  have hassoc (x y z : UInt256) : UInt256.land x (UInt256.land y z) =
      UInt256.land (UInt256.land x y) z := by
    apply u256_inj
    simp only [uland_toNat, Nat.and_assoc]
  have hlo : UInt256.land (amountDeltaNumerator a) (UInt256.ofNat (2 ^ 224 - 1)) =
      amountDeltaNumerator a :=
    u256LandMaskCleanOfToNat (bits := 224) _ _ (by decide) (amountDeltaNumerator_lt a hfit)
  rw [hmask, hassoc]
  change UInt256.land (UInt256.land (amountDeltaNumerator a) (UInt256.ofNat (2 ^ 224 - 1)))
    (UInt256.ofNat (2 ^ 256 - 2 ^ 96)) = _
  rw [hlo]
  apply u256_land_high_mask_eq_self (amountDeltaNumerator a) (k := 96) (by decide)
  rw [amountDeltaNumerator_toNat a hfit]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left _ _)

end Benchmarks.UniswapV3.Pool

import Benchmarks.UniswapV3.Pool.TickSqrtBounds
import Benchmarks.UniswapV3.Pool.FlashProtocolWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem tickSqrtInvert_lt192 (tick : Int) (ht : tick.natAbs ≤ 887272) :
    (tickSqrtInvert tick (tickSqrtRatio (UInt256.ofNat tick.natAbs))).toNat <
      2 ^ 192 - 2 ^ 32 := by
  have hlo := tickSqrtRatio_valid_lower tick.natAbs ht
  have hhi := (tickSqrtRatio_bounds (UInt256.ofNat tick.natAbs)).2
  unfold tickSqrtInvert
  split_ifs
  · rw [udiv_toNat, u256_lnot_zero_toNat]
    apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    calc
      UInt256.size - 1 < (2 ^ 192 - 2 ^ 32) * (2 ^ 64 + 1) := by decide +kernel
      _ ≤ (2 ^ 192 - 2 ^ 32) * (tickSqrtRatio (UInt256.ofNat tick.natAbs)).toNat :=
        Nat.mul_le_mul_left _ (by omega)
  · omega

theorem tickSqrtRaw_lt160 (tick : Int) (ht : tick.natAbs ≤ 887272) :
    (tickSqrtRaw tick).toNat < 2 ^ 160 := by
  have hb := tickSqrtInvert_lt192 tick ht
  unfold tickSqrtRaw tickSqrtRound
  rw [uadd_toNat, wordShiftRight_toNat _ _ (by decide)]
  split_ifs
  all_goals
    apply lt_of_le_of_lt (Nat.mod_le _ _)
    norm_num only [show (⟨32⟩ : UInt256).toNat = 32 from rfl,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨1⟩ : UInt256).toNat = 1 from rfl]
    omega

theorem tickSqrtValue_eq_raw (tick : Int) (ht : tick.natAbs ≤ 887272) :
    tickSqrtValue tick = tickSqrtRaw tick :=
  u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) (tickSqrtRaw_lt160 tick ht)

theorem tickSqrtValue_lt160 (tick : Int) : (tickSqrtValue tick).toNat < 2 ^ 160 :=
  u256LandMaskToNatLtOfToNat (bits := 160) _ _ (by decide)

end Benchmarks.UniswapV3.Pool

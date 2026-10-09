import Benchmarks.CompoundIII.Comet.ConstructorInitialImms

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def constructorScaleWord (w : UInt256) : UInt256 := UInt256.ofNat (10 ^ w.toNat)

theorem constructorScale_bound {w : UInt256} (hw : w.toNat ≤ 18) : 10 ^ w.toNat < 2^64 :=
  lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hw) (by decide)

theorem constructorScaleWord_toNat {w : UInt256} (hw : w.toNat ≤ 18) :
    (constructorScaleWord w).toNat = 10 ^ w.toNat :=
  UInt256.toNat_ofNat_of_lt (lt_trans (constructorScale_bound hw) (by decide))

theorem constructorScale_exp {w : UInt256} (hw : w.toNat ≤ 18) :
    UInt256.exp (UInt256.ofNat 10) w = constructorScaleWord w := by
  have he (n : Nat) (hn : n ≤ 18) :
      UInt256.exp (UInt256.ofNat 10) (UInt256.ofNat n) = UInt256.ofNat (10 ^ n) := by
    interval_cases n <;> decide +kernel
  have hr : UInt256.ofNat w.toNat = w := by
    apply u256_inj
    exact UInt256.toNat_ofNat_of_lt w.val.isLt
  exact (congrArg (UInt256.exp (UInt256.ofNat 10)) hr).symm.trans (he w.toNat hw)

theorem constructorScale_clean {w : UInt256} (hw : w.toNat ≤ 18) :
    UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))
      (UInt256.exp (UInt256.ofNat 10) (UInt256.land w (UInt256.ofNat 255))) =
      constructorScaleWord w := by
  rw [u256LandMaskCleanOfToNat (bits := 8) w _ (by decide) (by change _ < 256; omega),
    constructorScale_exp hw,
    u256_land_comm]
  exact u256LandMaskCleanOfToNat (bits := 64) _ _ (by native_decide)
    (by rw [constructorScaleWord_toNat hw]; exact constructorScale_bound hw)

theorem constructorScale_min {w : UInt256} (hw : w.toNat ≤ 18) :
    1000000 ≤ 10 ^ w.toNat ↔ 6 ≤ w.toNat := by
  generalize w.toNat = n at hw ⊢
  interval_cases n <;> decide +kernel

end Benchmarks.CompoundIII.Comet

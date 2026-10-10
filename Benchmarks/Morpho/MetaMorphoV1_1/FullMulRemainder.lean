import Benchmarks.Morpho.MetaMorphoV1_1.FullMulProduct

/-! Subtracting the division remainder from a two-word product. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

theorem subtractDoubleWord (high low rem : UInt256)
    (hr : rem.toNat ≤ high.toNat * UInt256.size + low.toNat) :
    (UInt256.sub high (UInt256.gt rem low)).toNat * UInt256.size +
        (UInt256.sub low rem).toNat =
      high.toNat * UInt256.size + low.toNat - rem.toNat := by
  by_cases hb : low.toNat < rem.toNat
  · have hhigh : 0 < high.toNat := by
      by_contra h
      have hz : high.toNat = 0 := Nat.eq_zero_of_not_pos h
      rw [hz, Nat.zero_mul, Nat.zero_add] at hr
      omega
    rw [ugt_one hb, usub_toNat (show (⟨1⟩ : UInt256).toNat ≤ high.toNat by exact hhigh),
      usub_toNat_underflow hb]
    have hh : high.toNat - 1 + 1 = high.toNat := Nat.sub_add_cancel hhigh
    have hrem : rem.toNat < UInt256.size := rem.val.isLt
    have hl : UInt256.size + low.toNat - rem.toNat + rem.toNat = UInt256.size + low.toNat :=
      Nat.sub_add_cancel (by omega)
    have hr' := Nat.sub_add_cancel hr
    change (high.toNat - 1) * UInt256.size + (UInt256.size + low.toNat - rem.toNat) = _
    nlinarith
  · have hle := Nat.le_of_not_gt hb
    rw [ugt_zero hle, uint256_sub_zero_right, usub_toNat hle]
    omega

def fullProductLowAdjusted (a b d : UInt256) : UInt256 :=
  UInt256.sub (UInt256.mul a b) (UInt256.mulMod a b d)

def fullProductHighAdjusted (a b d : UInt256) : UInt256 :=
  UInt256.sub (fullProductHigh a b) (UInt256.gt (UInt256.mulMod a b d) (UInt256.mul a b))

theorem fullProductAdjusted_decomposition (a b d : UInt256) (hd : d ≠ ⟨0⟩) :
    (fullProductHighAdjusted a b d).toNat * UInt256.size +
        (fullProductLowAdjusted a b d).toNat =
      a.toNat * b.toNat - (a.toNat * b.toNat) % d.toNat := by
  have hp : (fullProductHigh a b).toNat * UInt256.size + (UInt256.mul a b).toNat =
      a.toNat * b.toNat := by
    rw [fullProductHigh_toNat, u256_mul_toNat]
    simpa only [Nat.mul_comm] using Nat.div_add_mod (a.toNat * b.toNat) UInt256.size
  have hr : (UInt256.mulMod a b d).toNat ≤
      (fullProductHigh a b).toNat * UInt256.size + (UInt256.mul a b).toNat := by
    rw [hp, wordMulMod_toNat _ _ _ hd]
    exact Nat.mod_le _ _
  exact (subtractDoubleWord (fullProductHigh a b) (UInt256.mul a b)
    (UInt256.mulMod a b d) hr).trans (by rw [hp, wordMulMod_toNat _ _ _ hd])

theorem fullProductAdjusted_exact (a b d : UInt256) (hd : d ≠ ⟨0⟩) :
    (fullProductHighAdjusted a b d).toNat * UInt256.size +
        (fullProductLowAdjusted a b d).toNat =
      (a.toNat * b.toNat / d.toNat) * d.toNat := by
  rw [fullProductAdjusted_decomposition a b d hd]
  have h : (a.toNat * b.toNat / d.toNat) * d.toNat +
      (a.toNat * b.toNat) % d.toNat = a.toNat * b.toNat := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod (a.toNat * b.toNat) d.toNat
  omega

end Benchmarks.Morpho.MetaMorphoV1_1

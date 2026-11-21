import Benchmarks.Midnight.LiquidateConversion

/-! Arithmetic of the recovery-threshold branch's maximum repayment. -/

open Ethereum Reasoning.Theory

namespace Benchmarks.Midnight

def liquidateRcfDenominator (lif lltv : UInt256) : UInt256 :=
  UInt256.sub liquidatePriceScale (UInt256.mul lif lltv)

def liquidateMaxRepaid (debt maxDebt lif lltv : UInt256) : UInt256 :=
  mulDivUp (UInt256.sub debt maxDebt) liquidatePriceScale (liquidateRcfDenominator lif lltv)

def LiquidateMaxRepaidSafe (debt maxDebt lif lltv : UInt256) : Prop :=
  maxDebt.toNat ≤ debt.toNat ∧ lif.toNat * lltv.toNat < UInt256.size ∧
    (UInt256.mul lif lltv).toNat < liquidatePriceScale.toNat

theorem lifScale_squared : UInt256.mul lifScale lifScale = liquidatePriceScale := by decide +kernel

theorem liquidatePriceScale_mul_fit {x : UInt256} (hx : x.toNat < 2 ^ 128) :
    x.toNat * liquidatePriceScale.toNat < UInt256.size := by
  change x.toNat * 1000000000000000000000000000000000000 < 2 ^ 256
  omega

theorem liquidateScaledRatioSafe {x denominator : UInt256} (hx : x.toNat < 2 ^ 128)
    (hp : 0 < denominator.toNat) (hd : denominator.toNat ≤ liquidatePriceScale.toNat) :
    MulDivUpSafe x liquidatePriceScale denominator := by
  have hmul := liquidatePriceScale_mul_fit hx
  refine ⟨hmul, hp, ?_⟩
  rw [u256_mul_toNat, Nat.mod_eq_of_lt hmul,
    usub_toNat (a := denominator) (b := ⟨1⟩) hp]
  change x.toNat * 1000000000000000000000000000000000000 + (denominator.toNat - 1) < 2 ^ 256
  change denominator.toNat ≤ 1000000000000000000000000000000000000 at hd
  omega

theorem liquidateMaxRepaid_mulDivSafe {debt maxDebt lif lltv : UInt256}
    (hd : debt.toNat < 2 ^ 128) (hm : maxDebt.toNat ≤ debt.toNat)
    (hp : (UInt256.mul lif lltv).toNat < liquidatePriceScale.toNat) :
    MulDivUpSafe (UInt256.sub debt maxDebt) liquidatePriceScale
      (liquidateRcfDenominator lif lltv) := by
  have hshort : (UInt256.sub debt maxDebt).toNat < 2 ^ 128 := by
    rw [usub_toNat hm]; omega
  have hden : (liquidateRcfDenominator lif lltv).toNat =
      liquidatePriceScale.toNat - (UInt256.mul lif lltv).toNat := usub_toNat (Nat.le_of_lt hp)
  have hpos : 0 < (liquidateRcfDenominator lif lltv).toNat := by rw [hden]; omega
  have hdenBound : (liquidateRcfDenominator lif lltv).toNat ≤
      1000000000000000000000000000000000000 := by
    rw [hden]
    change 1000000000000000000000000000000000000 - _ ≤ _
    omega
  exact liquidateScaledRatioSafe hshort hpos hdenBound

end Benchmarks.Midnight

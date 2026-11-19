import Benchmarks.Midnight.MulDiv
import Benchmarks.Midnight.Uint128Arithmetic

/-! Bounds for the loss-factor update after bad debt is deducted from total units. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def liquidateLossQuotient (total loss badDebt : UInt256) : UInt256 :=
  mulDivDown (complement128 loss) (UInt256.sub total badDebt) total

def liquidateNextLoss (total loss badDebt : UInt256) : UInt256 :=
  complement128 (liquidateLossQuotient total loss badDebt)

-- LIBRARY CANDIDATE: a bounded product divided by at least its second factor is at most its first.
theorem mulDivDown_le_left {a b d : UInt256}
    (hfit : a.toNat * b.toNat < UInt256.size) (hle : b.toNat ≤ d.toNat) :
    (mulDivDown a b d).toNat ≤ a.toNat := by
  rw [mulDivDown, udiv_toNat]
  change (a * b).toNat / d.toNat ≤ a.toNat
  rw [umul_toNat _ _ hfit]
  apply Nat.div_le_of_le_mul
  simpa only [Nat.mul_comm d.toNat] using Nat.mul_le_mul_left a.toNat hle

theorem liquidateLossProduct_lt {total loss badDebt : UInt256}
    (ht : total.toNat < 2 ^ 128) (hl : loss.toNat < 2 ^ 128)
    (hle : badDebt.toNat ≤ total.toNat) :
    (complement128 loss).toNat * (UInt256.sub total badDebt).toNat < UInt256.size :=
  uint128_product_bound (complement128_lt hl) (by rw [usub_toNat hle]; omega)

theorem liquidateLossQuotient_lt {total loss badDebt : UInt256}
    (ht : total.toNat < 2 ^ 128) (hl : loss.toNat < 2 ^ 128)
    (hle : badDebt.toNat ≤ total.toNat) :
    (liquidateLossQuotient total loss badDebt).toNat < 2 ^ 128 :=
  (mulDivDown_le_left (liquidateLossProduct_lt ht hl hle)
    (by rw [usub_toNat hle]; omega)).trans_lt (complement128_lt hl)

theorem liquidateNextLoss_lt {total loss badDebt : UInt256}
    (ht : total.toNat < 2 ^ 128) (hl : loss.toNat < 2 ^ 128)
    (hle : badDebt.toNat ≤ total.toNat) :
    (liquidateNextLoss total loss badDebt).toNat < 2 ^ 128 :=
  complement128_lt (liquidateLossQuotient_lt ht hl hle)

end Benchmarks.Midnight

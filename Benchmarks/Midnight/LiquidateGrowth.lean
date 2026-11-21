import Benchmarks.Midnight.MaxLifTrace
import Benchmarks.Midnight.WordMin
import Benchmarks.Midnight.WordComplementSub

/-! Post-maturity incentive growth and its checked-arithmetic conditions. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def liquidateGrowthProduct (maximum timestamp maturity : UInt256) : UInt256 :=
  UInt256.mul (UInt256.sub maximum lifScale) (UInt256.sub timestamp maturity)

def liquidateGrowth (maximum timestamp maturity : UInt256) : UInt256 :=
  lifScale + UInt256.div (liquidateGrowthProduct maximum timestamp maturity) ⟨3600⟩

def liquidateGrownLif (maximum timestamp maturity : UInt256) : UInt256 :=
  wordMin maximum (liquidateGrowth maximum timestamp maturity)

def LiquidateGrowthSafe (maximum timestamp maturity : UInt256) : Prop :=
  lifScale.toNat ≤ maximum.toNat ∧ maturity.toNat ≤ timestamp.toNat ∧
    (UInt256.sub maximum lifScale).toNat * (UInt256.sub timestamp maturity).toNat < UInt256.size

instance (maximum timestamp maturity : UInt256) :
    Decidable (LiquidateGrowthSafe maximum timestamp maturity) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem wordSubLifScale (maximum : UInt256) :
    maximum + UInt256.lnot (UInt256.ofNat 999999999999999999) =
      UInt256.sub maximum lifScale :=
  wordAddLnotOfNat maximum 999999999999999999 (by decide)

theorem liquidateGrowth_add_fit (product : UInt256) :
    lifScale.toNat + (UInt256.div product ⟨3600⟩).toNat < UInt256.size := by
  have hp := product.val.isLt
  change product.toNat < 2 ^ 256 at hp
  rw [udiv_toNat]
  change 1000000000000000000 + product.toNat / 3600 < 2 ^ 256
  omega

-- GENERALIZES wordMin_branchless to the commuted final XOR emitted at pc 6630.
theorem wordMin_branchless_commuted (x y : UInt256) :
    UInt256.xor (UInt256.mul (UInt256.xor x y) (UInt256.lt y x)) x = wordMin x y := by
  rw [← wordMin_branchless]
  apply u256_inj
  change (_ ^^^ _) % UInt256.size = (_ ^^^ _) % UInt256.size
  rw [Nat.xor_comm]

end Benchmarks.Midnight

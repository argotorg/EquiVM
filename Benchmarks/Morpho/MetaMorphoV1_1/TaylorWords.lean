import Benchmarks.Morpho.MetaMorphoV1_1.WadMultiply

/-! The three Taylor terms and the overflow conditions of their compiled calculation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def taylorSecond (first : UInt256) : UInt256 :=
  UInt256.div (UInt256.mul first first) (UInt256.ofNat (2 * 10 ^ 18))

def taylorThird (first : UInt256) : UInt256 :=
  UInt256.div (UInt256.mul (taylorSecond first) first) (UInt256.ofNat (3 * 10 ^ 18))

def taylorSum (first : UInt256) : UInt256 := first + taylorSecond first + taylorThird first

def taylorTailFits (first : UInt256) : Prop :=
  first.toNat * first.toNat < UInt256.size ∧
    (taylorSecond first).toNat * first.toNat < UInt256.size

def taylorFits (x n : UInt256) : Prop :=
  x.toNat * n.toNat < UInt256.size ∧ taylorTailFits (UInt256.mul x n)

instance (first : UInt256) : Decidable (taylorTailFits first) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (x n : UInt256) : Decidable (taylorFits x n) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- The division bounds ensure neither final addition can overflow once first^2 fits.
theorem taylorSumsFit (first : UInt256) (hsq : first.toNat * first.toNat < UInt256.size) :
    first.toNat + (taylorSecond first).toNat < UInt256.size ∧
      (first + taylorSecond first).toNat + (taylorThird first).toNat < UInt256.size := by
  have hfirst : first.toNat < 2 ^ 128 := by
    change first.toNat * first.toNat < 2 ^ 256 at hsq
    by_contra h
    have hl : 2 ^ 128 ≤ first.toNat := by omega
    nlinarith
  have hsecond : (taylorSecond first).toNat < 2 ^ 200 := by
    rw [taylorSecond, udiv_toNat]
    change (UInt256.mul first first).toNat / (2 * 10 ^ 18) < 2 ^ 200
    apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
    exact lt_trans (UInt256.mul first first).val.isLt (by decide)
  have hthird : (taylorThird first).toNat < 2 ^ 200 := by
    rw [taylorThird, udiv_toNat]
    change (UInt256.mul (taylorSecond first) first).toNat / (3 * 10 ^ 18) < 2 ^ 200
    apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
    exact lt_trans (UInt256.mul (taylorSecond first) first).val.isLt (by decide)
  have hsum : first.toNat + (taylorSecond first).toNat < UInt256.size := by
    change _ < 2 ^ 256; omega
  refine ⟨hsum, ?_⟩
  rw [uadd_toNat, Nat.mod_eq_of_lt hsum]
  change _ < 2 ^ 256
  omega

end Benchmarks.Morpho.MetaMorphoV1_1

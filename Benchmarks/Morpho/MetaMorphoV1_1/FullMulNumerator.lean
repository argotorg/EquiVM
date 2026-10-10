import Benchmarks.Morpho.MetaMorphoV1_1.FullMulRemainder
import Benchmarks.Morpho.MetaMorphoV1_1.FullMulInverse

/-! Combining the two corrected product words after removing powers of two. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def fullDivTwosComplement (d : UInt256) : UInt256 :=
  UInt256.div (UInt256.sub ⟨0⟩ (fullDivTwos d)) (fullDivTwos d) + ⟨1⟩

theorem fullDivTwosComplement_toNat {d : UInt256} {k : Nat} (hk : k < 256)
    (ht : (fullDivTwos d).toNat = 2 ^ k) :
    (fullDivTwosComplement d).toNat = 2 ^ (256 - k) % UInt256.size := by
  have hpos : 0 < (fullDivTwos d).toNat := by rw [ht]; exact Nat.two_pow_pos _
  have hsize : UInt256.size = 2 ^ (256 - k) * 2 ^ k := by
    change 2 ^ 256 = _
    rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hk)]
  have hquot : UInt256.size / 2 ^ k = 2 ^ (256 - k) := by
    rw [hsize, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  have hsub : (UInt256.size - 2 ^ k) / 2 ^ k = UInt256.size / 2 ^ k - 1 := by
    simpa only [Nat.mul_one] using Nat.sub_mul_div UInt256.size (2 ^ k) 1
  rw [fullDivTwosComplement, uadd_toNat, udiv_toNat,
    usub_toNat_underflow (show (⟨0⟩ : UInt256).toNat < (fullDivTwos d).toNat from hpos), ht]
  change ((UInt256.size - 2 ^ k) / 2 ^ k + 1) % UInt256.size = _
  rw [hsub, hquot, Nat.sub_add_cancel (Nat.two_pow_pos _)]

theorem fullDivCombineWords {low high twos complement : UInt256} {k : Nat} (hk : k < 256)
    (ht : twos.toNat = 2 ^ k) (hc : complement.toNat = 2 ^ (256 - k) % UInt256.size) :
    (UInt256.lor (UInt256.div low twos) (UInt256.mul high complement)).toNat =
      ((high.toNat * UInt256.size + low.toNat) / 2 ^ k) % UInt256.size := by
  have hsize : UInt256.size = 2 ^ (256 - k) * 2 ^ k := by
    change 2 ^ 256 = _
    rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hk)]
  have hlo : low.toNat / 2 ^ k < 2 ^ (256 - k) := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    rw [← hsize]
    exact low.val.isLt
  have hhigh : high.toNat * 2 ^ (256 - k) % UInt256.size =
      (high.toNat % 2 ^ k) * 2 ^ (256 - k) := by
    rw [hsize, Nat.mul_comm (2 ^ (256 - k)) (2 ^ k), Nat.mul_mod_mul_right]
  have hdiv : (high.toNat * UInt256.size + low.toNat) / 2 ^ k =
      low.toNat / 2 ^ k + high.toNat * 2 ^ (256 - k) := by
    rw [hsize, ← Nat.mul_assoc, Nat.add_comm,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)]
  rw [u256_lor_toNat, udiv_toNat, u256_mul_toNat, ht, hc, Nat.mul_mod_mod, hhigh]
  rw [nat_lor_shift_add _ _ _ hlo, hdiv, ← hhigh, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

def fullDivNumerator (a b d : UInt256) : UInt256 :=
  UInt256.lor (UInt256.div (fullProductLowAdjusted a b d) (fullDivTwos d))
    (UInt256.mul (fullProductHighAdjusted a b d) (fullDivTwosComplement d))

theorem fullDivNumerator_toNat {a b d : UInt256} {k m : Nat} (hd : d ≠ ⟨0⟩)
    (hk : k < 256) (he : d.toNat = 2 ^ k * m) (ht : (fullDivTwos d).toNat = 2 ^ k) :
    (fullDivNumerator a b d).toNat = (a.toNat * b.toNat / d.toNat * m) % UInt256.size := by
  rw [fullDivNumerator, fullDivCombineWords hk ht (fullDivTwosComplement_toNat hk ht),
    fullProductAdjusted_exact a b d hd]
  congr 1
  rw [he, Nat.mul_comm (2 ^ k) m, ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

def fullMulDivCalculated (a b d : UInt256) : UInt256 :=
  UInt256.mul (fullDivNumerator a b d) (fullDivInverse (UInt256.div d (fullDivTwos d)) 6)

theorem fullMulDivCalculated_correct (a b d : UInt256) (hd : d ≠ ⟨0⟩) :
    fullMulDivCalculated a b d = fullMulDivWord a b d := by
  obtain ⟨k, m, hk, hm, he, ht⟩ := fullDivTwos_decomposition d hd
  have hden : (UInt256.div d (fullDivTwos d)).toNat = m := by
    rw [udiv_toNat, ht, he, Nat.mul_comm, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  have hodd : Odd (UInt256.div d (fullDivTwos d)).toNat := by rw [hden]; exact hm
  have hnum : wordResidue (fullDivNumerator a b d) =
      wordResidue (fullMulDivWord a b d) * wordResidue (UInt256.div d (fullDivTwos d)) := by
    apply ZMod.val_injective UInt256.size
    rw [ZMod.val_mul]
    change (fullDivNumerator a b d).toNat =
      (fullMulDivWord a b d).toNat * (UInt256.div d (fullDivTwos d)).toNat % UInt256.size
    rw [fullDivNumerator_toNat hd hk he ht, hden]
    change _ = ((a.toNat * b.toNat / d.toNat) % UInt256.size * m) % UInt256.size
    rw [Nat.mod_mul_mod]
  have hinv := congrArg wordResidue (fullDivInverse_correct (UInt256.div d (fullDivTwos d)) hodd)
  rw [wordResidue_mul] at hinv
  change wordResidue (UInt256.div d (fullDivTwos d)) *
    wordResidue (fullDivInverse (UInt256.div d (fullDivTwos d)) 6) = 1 at hinv
  apply wordResidue_injective
  rw [fullMulDivCalculated, wordResidue_mul, hnum, mul_assoc, hinv, mul_one]

end Benchmarks.Morpho.MetaMorphoV1_1

import Benchmarks.UniswapV4PoolManager.SignedDivisionWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

-- LIBRARY CANDIDATE: the EVM's auxiliary signed conversion agrees with modular encoding in range.
theorem toSigned_eq_wordOfInt {i : Int} (hi : -(2^256 : Int) ≤ i) :
    UInt256.toSigned i = EVM.wordOfInt i := by
  cases i with
  | ofNat n => exact (wordOfInt_ofNat_toNat_gen n).symm
  | negSucc n =>
    rw [wordOfInt_eq_mod, UInt256.toSigned]
    apply congrArg UInt256.ofNat
    change 2^256-1-n = (Int.negSucc n % (2^256 : Int)).toNat
    omega

-- LIBRARY CANDIDATE: unsigned remainder agrees with natural remainder for nonzero divisors.
theorem wordMod_toNat {a b : UInt256} (hb : b.toNat ≠ 0) :
    (UInt256.mod a b).toNat = a.toNat % b.toNat := by
  have hv : b.val ≠ 0 := by
    intro h
    apply hb
    exact congrArg Fin.val h
  unfold UInt256.mod
  rw [if_neg (by simpa only [beq_iff_eq] using hv)]
  rfl

-- LIBRARY CANDIDATE: SMOD is the encoded truncating remainder, with its EVM zero-divisor rule.
theorem smod_signed (a b : UInt256) :
    UInt256.smod a b = if b = ⟨0⟩ then ⟨0⟩ else EVM.wordOfInt ((EVM.signed a).tmod (EVM.signed b)) := by
  by_cases hz : b = ⟨0⟩
  · subst b
    rw [if_pos rfl]
    rfl
  · rw [if_neg hz]
    have hb : b.toNat ≠ 0 := fun he => hz (uint256_toNat_eq_zero he)
    have hab : (UInt256.abs b).toNat ≠ 0 := by
      by_cases hh : 2^255 ≤ b.toNat
      · rw [u256_abs_high_toNat hh (by omega)]
        have hsize := b.val.isLt
        change b.toNat < UInt256.size at hsize
        omega
      · simpa only [UInt256.abs, if_neg hh] using hb
    have hm := wordMod_toNat (a := UInt256.abs a) hab
    have hrange : (UInt256.abs a).toNat % (UInt256.abs b).toNat < 2^256 :=
      lt_of_le_of_lt (Nat.mod_le _ _) (UInt256.abs a).val.isLt
    have hlow (w : UInt256) (hw : ¬2^255 ≤ w.toNat) : EVM.signed w = Int.ofNat w.toNat := by
      change (if w.toNat < 2^255 then _ else _) = _
      rw [if_pos (by omega)]
      rfl
    have hrem (x y : Nat) : (Int.ofNat x).tmod (Int.ofNat y) = Int.ofNat (x%y) := rfl
    unfold UInt256.smod
    rw [if_neg (by simpa only [beq_iff_eq] using hb)]
    change UInt256.toSigned (UInt256.sgn a * Int.ofNat (UInt256.mod (UInt256.abs a) (UInt256.abs b)).toNat) = _
    rw [hm]
    by_cases ha : 2^255 ≤ a.toNat
    · rw [UInt256.sgn, if_pos ha, neg_one_mul, toSigned_eq_wordOfInt (by
        simp only [Int.ofNat_eq_natCast]; omega), signed_eq_neg_abs ha, Int.neg_tmod]
      by_cases hbhi : 2^255 ≤ b.toNat
      · rw [signed_eq_neg_abs hbhi, Int.tmod_neg, hrem]
      · rw [hlow b hbhi, hrem]
        simp only [UInt256.abs, if_neg hbhi]
    · have haabs : UInt256.abs a = a := by rw [UInt256.abs, if_neg ha]
      rw [UInt256.sgn, if_neg ha, hlow a ha, haabs]
      by_cases haz : UInt256.eq0 a = true
      · have hae : a = ⟨0⟩ := by simpa only [UInt256.eq0, beq_iff_eq] using haz
        subst a
        simp only [haz, if_true, zero_mul]
        change UInt256.toSigned 0 = EVM.wordOfInt ((0 : Int).tmod (EVM.signed b))
        rw [Int.zero_tmod]
        rfl
      · rw [if_neg haz, one_mul, toSigned_eq_wordOfInt (by simp only [Int.ofNat_eq_natCast]; omega)]
        by_cases hbhi : 2^255 ≤ b.toNat
        · rw [signed_eq_neg_abs hbhi, Int.tmod_neg, hrem]
        · rw [hlow b hbhi, hrem]
          simp only [UInt256.abs, if_neg hbhi]

-- LIBRARY CANDIDATE: a truncating remainder stays in signed range when its dividend does.
theorem tmod_int256_of_abs_lt {x : Int} (y : Int) (hx : x.natAbs < 2^255) :
    int256Fits (x.tmod y) := by
  have hb : (x.tmod y).natAbs ≤ x.natAbs := by
    rw [Int.natAbs_tmod]
    exact Nat.mod_le _ _
  have hhi := Int.le_natAbs (a := x.tmod y)
  have hlo := Int.le_natAbs (a := -(x.tmod y))
  rw [Int.natAbs_neg] at hlo
  change -(2^255 : Int) ≤ x.tmod y ∧ x.tmod y < (2^255 : Int)
  omega

end Benchmarks.UniswapV4PoolManager

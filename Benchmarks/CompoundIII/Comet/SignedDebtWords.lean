import Benchmarks.CompoundIII.Comet.SignedWord

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: signed comparison in terms of the mathematical signed values.
theorem signedWord_slt (a b : UInt256) :
    UInt256.slt a b = UInt256.fromBool (decide (signedWord a < signedWord b)) := by
  rw [← signedWord_sgt b a]
  unfold UInt256.slt UInt256.sgt UInt256.sltBool UInt256.sgtBool
  by_cases ha : 2^255 ≤ a.toNat <;> by_cases hb : 2^255 ≤ b.toNat <;>
    simp only [ha, hb, if_true, if_false]

-- GENERALIZES signedWord_sub_low to include the minimum signed integer.
theorem signedWord_zeroSub_le {m : UInt256} (hm : m.toNat ≤ 2^255) :
    signedWord (UInt256.sub (UInt256.ofNat 0) m) = -Int.ofNat m.toNat := by
  by_cases hz : m = UInt256.ofNat 0
  · subst m
    decide
  · have hp : 0 < m.toNat := Nat.pos_of_ne_zero (fun h ↦ hz (uint256_toNat_eq_zero h))
    rw [signedWord_eq, usub_toNat_underflow (a := UInt256.ofNat 0) (b := m) hp]
    change (if 2^256 - m.toNat < 2^255 then _ else _) = _
    rw [if_neg (by omega)]
    change ((2^256 - m.toNat : Nat) : Int) - (2^256 : Int) = -(m.toNat : Int)
    omega

-- LIBRARY CANDIDATE: the EVM absolute value of a bounded negative encoding.
theorem wordAbs_zeroSub_le {m : UInt256} (hm : m.toNat ≤ 2^255) :
    UInt256.abs (UInt256.sub (UInt256.ofNat 0) m) = m := by
  by_cases hz : m = UInt256.ofNat 0
  · subst m
    decide
  · have hp : 0 < m.toNat := Nat.pos_of_ne_zero (fun h ↦ hz (uint256_toNat_eq_zero h))
    have hn : (UInt256.sub (UInt256.ofNat 0) m).toNat = 2^256 - m.toNat :=
      usub_toNat_underflow hp
    apply u256_inj
    rw [u256_abs_high_toNat (by rw [hn]; omega) (by rw [hn]; omega), hn]
    change 2^256 - (2^256 - m.toNat) = m.toNat
    omega

-- GENERALIZES u256_sdiv_high_low to include zero and identify the negative quotient.
theorem wordSdiv_zeroSub_low {m d : UInt256} (hm : m.toNat ≤ 2^255)
    (hd : d.toNat < 2^255) :
    UInt256.sdiv (UInt256.sub (UInt256.ofNat 0) m) d =
      UInt256.sub (UInt256.ofNat 0) (UInt256.div m d) := by
  by_cases hz : m = UInt256.ofNat 0
  · subst m
    rw [u256_sub_self, u256_sdiv_zero_left]
    have hz : UInt256.div (UInt256.ofNat 0) d = UInt256.ofNat 0 := u256_div_zero_left d
    rw [hz, u256_sub_self]
  · have hp : 0 < m.toNat := Nat.pos_of_ne_zero (fun h ↦ hz (uint256_toNat_eq_zero h))
    have hn : 2^255 ≤ (UInt256.sub (UInt256.ofNat 0) m).toNat := by
      rw [usub_toNat_underflow (a := UInt256.ofNat 0) (b := m) hp]
      change 2^255 ≤ 2^256 - m.toNat
      omega
    rw [u256_sdiv_high_low hn hd, wordAbs_zeroSub_le hm]
    apply congrArg UInt256.mk
    change (UInt256.div m d).val * -1 = 0 - (UInt256.div m d).val
    rw [mul_neg_one, zero_sub]

-- LIBRARY CANDIDATE: modular multiplication respects the negative encoding.
theorem wordMul_zeroSub (m p : UInt256) :
    UInt256.mul (UInt256.sub (UInt256.ofNat 0) m) p =
      UInt256.sub (UInt256.ofNat 0) (UInt256.mul m p) := by
  apply congrArg UInt256.mk
  change (0 - m.val) * p.val = 0 - m.val * p.val
  rw [sub_mul, zero_mul]

-- LIBRARY CANDIDATE: the signed multiplication guard for a nonpositive left operand.
theorem signedDebtMulGuard (m p : UInt256) (hm : m.toNat ≤ 2^255)
    (hp : 0 < p.toNat) (hp' : p.toNat < 2^255) :
    UInt256.slt (UInt256.sub (UInt256.ofNat 0) m)
      (UInt256.sdiv (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)) p) =
      UInt256.fromBool (decide (2^255 < m.toNat * p.toNat)) := by
  have hmin : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255) =
      UInt256.sub (UInt256.ofNat 0) (UInt256.ofNat (2^255)) := by decide
  have hq : (UInt256.div (UInt256.ofNat (2^255)) p).toNat ≤ 2^255 := by
    rw [udiv_toNat]
    exact Nat.div_le_self _ _
  rw [hmin, wordSdiv_zeroSub_low (by decide) hp', signedWord_slt,
    signedWord_zeroSub_le hm, signedWord_zeroSub_le hq, udiv_toNat]
  apply congrArg UInt256.fromBool
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Int.ofNat_eq_natCast, neg_lt_neg_iff, Int.ofNat_lt]
  exact Nat.div_lt_iff_lt_mul hp

end Benchmarks.CompoundIII.Comet

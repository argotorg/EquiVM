import Benchmarks.CompoundIII.Comet.SignedFields

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: full-width signed word interpretation and comparison.
def signedWord (w : UInt256) : Int := (⟨w.val⟩ : BitVec 256).toInt

theorem signedWord_bounds (w : UInt256) :
    -(2^255 : Int) ≤ signedWord w ∧ signedWord w < (2^255 : Int) :=
  ⟨BitVec.le_toInt _, BitVec.toInt_lt⟩

theorem signedWord_eq (w : UInt256) :
    signedWord w = if w.toNat < 2^255 then Int.ofNat w.toNat
      else Int.ofNat w.toNat - (2^256 : Int) := by
  unfold signedWord
  rw [BitVec.toInt_eq_toNat_cond]
  change (if 2 * w.toNat < 2^256 then _ else _) = _
  congr 1
  apply propext
  omega

theorem signedWord_low {w : UInt256} (hw : w.toNat < 2^255) :
    signedWord w = Int.ofNat w.toNat := by rw [signedWord_eq, if_pos hw]

-- LIBRARY CANDIDATE: the sign bit characterizes a nonnegative signed word.
theorem signedWord_nonneg_iff (w : UInt256) :
    0 ≤ signedWord w ↔ w.toNat < 2^255 := by
  rw [signedWord_eq]
  have hw : w.toNat < 2^256 := w.val.isLt
  split_ifs <;> simp only [Int.ofNat_eq_natCast] <;> omega

theorem signedWord_encode (w : UInt256) : EVM.wordOfInt (signedWord w) = w :=
  bitvecWordOfInt ⟨w.val⟩

theorem signedWordReturnEncoding (w : UInt256) :
    encodeReturnValue? (.elem (.int (.sint ⟨256, by decide⟩))) (.int (signedWord w)) =
      some w.toByteArray := by
  refine scalarReturnEncoding (t := .int (.sint ⟨256, by decide⟩)) (w := w) rfl ?_ ?_
  · simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
    decide
  · have hb : -(Int.ofNat (EVM.twoPow 255)) ≤ signedWord w ∧
        signedWord w < Int.ofNat (EVM.twoPow 255) := signedWord_bounds w
    simp only [encodeABIValue?, encodeABIWord?, show (256 : Nat) ≠ 0 from by decide,
      if_false, hb, if_true, signedWord_encode]
    rfl

theorem signedWord_sgt (a b : UInt256) :
    UInt256.sgt a b = UInt256.fromBool (decide (signedWord b < signedWord a)) := by
  unfold UInt256.sgt UInt256.sgtBool
  rw [signedWord_eq a, signedWord_eq b]
  have ha := a.val.isLt
  have hb := b.val.isLt
  change a.toNat < 2^256 at ha
  change b.toNat < 2^256 at hb
  by_cases hsa : a.toNat < 2^255 <;> by_cases hsb : b.toNat < 2^255 <;>
    simp only [hsa, hsb, ite_true, ite_false,
      show a.toNat ≥ 2^255 ↔ ¬ a.toNat < 2^255 from by omega,
      show b.toNat ≥ 2^255 ↔ ¬ b.toNat < 2^255 from by omega,
      hsa, hsb, not_true_eq_false, not_false_eq_true, ite_true, ite_false]
  all_goals congr 1
  all_goals simp only [Int.ofNat_eq_natCast]
  · congr 1
    apply propext
    change b.toNat < a.toNat ↔ _
    omega
  · exact (decide_eq_true (by omega)).symm
  · exact (decide_eq_false (by omega)).symm
  · congr 1
    apply propext
    change b.toNat < a.toNat ↔ _
    omega

theorem signedWord_sub_low {a b : UInt256} (ha : a.toNat < 2^255)
    (hb : b.toNat < 2^255) :
    signedWord (UInt256.sub a b) = Int.ofNat a.toNat - Int.ofNat b.toNat := by
  rw [signedWord_eq]
  simp only [Int.ofNat_eq_natCast]
  by_cases hle : b.toNat ≤ a.toNat
  · rw [usub_toNat hle, if_pos (by omega)]
    omega
  · rw [usub_toNat_underflow (Nat.lt_of_not_ge hle)]
    change (if 2^256 + a.toNat - b.toNat < 2^255 then _ else _) = _
    rw [if_neg (by omega)]
    change ((2^256 + a.toNat - b.toNat : Nat) : Int) - (2^256 : Int) = _
    omega

theorem signedWord_mod (w : UInt256) :
    signedWord w % (2^256 : Int) = Int.ofNat w.toNat := by
  rw [signedWord_eq]
  have hw := w.val.isLt
  change w.toNat < 2^256 at hw
  simp only [Int.ofNat_eq_natCast]
  split_ifs <;> omega

theorem signedWord_add_of_range {a b : UInt256}
    (hlo : -(2^255 : Int) ≤ signedWord a + Int.ofNat b.toNat)
    (hhi : signedWord a + Int.ofNat b.toNat < (2^255 : Int)) :
    signedWord (a + b) = signedWord a + Int.ofNat b.toNat := by
  have hm : (signedWord a + Int.ofNat b.toNat) % Int.ofNat EVM.wordModulus =
      Int.ofNat (a + b).toNat := by
    rw [uadd_toNat]
    have hma := signedWord_mod a
    change (signedWord a + Int.ofNat b.toNat) % (2^256 : Int) =
      Int.ofNat ((a.toNat + b.toNat) % 2^256)
    simp only [Int.ofNat_eq_natCast] at *
    omega
  rw [signedWord_eq]
  exact (int_eq_signed_word_of_range_mod hlo hhi hm).symm

-- GENERALIZES evalExpr_s256_ok/revert from Reasoning.SolmArithmetic to arbitrary frames.
theorem signedRangeSourceOk {cfg frame evm expr i}
    (he : evalExpr? cfg frame evm expr = .ok (.int i))
    (hlo : -(2^255 : Int) ≤ i) (hhi : i < (2^255 : Int)) :
    evalExpr? cfg frame evm (.inRange (.sint ⟨256, by decide⟩) expr) = .ok (.int i) := by
  have h0 : ¬ i < -(2^255 : Int) := by omega
  have h1 : ¬ i ≥ (2^255 : Int) := by omega
  simp only [evalExpr?, he, bind, EvalResult.bind, h0, h1, decide_false,
    Bool.or_self, Bool.false_eq_true, if_false, pure]

theorem signedRangeSourceOverflow {cfg frame evm expr i}
    (he : evalExpr? cfg frame evm expr = .ok (.int i))
    (hhi : (2^255 : Int) ≤ i) :
    evalExpr? cfg frame evm (.inRange (.sint ⟨256, by decide⟩) expr) = .revert := by
  simp only [evalExpr?, he, bind, EvalResult.bind, hhi, decide_true, Bool.or_true, if_true]

end Benchmarks.CompoundIII.Comet

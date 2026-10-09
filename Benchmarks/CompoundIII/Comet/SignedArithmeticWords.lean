import Benchmarks.CompoundIII.Comet.Signed104Encoding

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES signedWord_add_of_range to a signed right operand.
theorem signedWord_add_signed_of_range {a b : UInt256}
    (hlo : -(2^255 : Int) ≤ signedWord a + signedWord b)
    (hhi : signedWord a + signedWord b < (2^255 : Int)) :
    signedWord (a + b) = signedWord a + signedWord b := by
  have hm : (signedWord a + signedWord b) % Int.ofNat EVM.wordModulus =
      Int.ofNat (a + b).toNat := by
    have ha := signedWord_mod a
    have hb := signedWord_mod b
    rw [uadd_toNat]
    change (signedWord a + signedWord b) % (2^256 : Int) =
      Int.ofNat ((a.toNat + b.toNat) % 2^256)
    simp only [Int.ofNat_eq_natCast] at *
    omega
  rw [signedWord_eq]
  exact (int_eq_signed_word_of_range_mod hlo hhi hm).symm

-- GENERALIZES signedWord_sub_low to arbitrary signed operands whose difference fits.
theorem signedWord_sub_of_range {a b : UInt256}
    (hlo : -(2^255 : Int) ≤ signedWord a - signedWord b)
    (hhi : signedWord a - signedWord b < (2^255 : Int)) :
    signedWord (UInt256.sub a b) = signedWord a - signedWord b := by
  have hm : (signedWord a - signedWord b) % Int.ofNat EVM.wordModulus =
      Int.ofNat (UInt256.sub a b).toNat := by
    have hs := signedSubWrap a b (signedWord b) (signedWord_mod b)
    have ha := signedWord_mod a
    change (signedWord a - signedWord b) % (2^256 : Int) = _
    change (Int.ofNat a.toNat - signedWord b) % (2^256 : Int) = _ at hs
    simp only [Int.ofNat_eq_natCast] at *
    omega
  rw [signedWord_eq]
  exact (int_eq_signed_word_of_range_mod hlo hhi hm).symm

-- LIBRARY CANDIDATE: signed subtraction of packed 104-bit operands is exact at word width.
theorem signed104_sub_word (a b : UInt256) :
    signedWord (UInt256.sub (UInt256.signextend (UInt256.ofNat 12) a)
      (UInt256.signextend (UInt256.ofNat 12) b)) = signed104 a - signed104 b := by
  have ha := signed104_bounds a
  have hb := signed104_bounds b
  rw [signedWord_sub_of_range, signedWord_signextend104, signedWord_signextend104]
  all_goals rw [signedWord_signextend104, signedWord_signextend104]; omega

-- GENERALIZES signedRangeSourceOk to any signed width.
theorem signedNarrowRangeSourceOk {cfg frame evm expr i} (width : BitWidth)
    (he : evalExpr? cfg frame evm expr = .ok (.int i))
    (hlo : -(2^(width.val-1) : Int) ≤ i) (hhi : i < (2^(width.val-1) : Int)) :
    evalExpr? cfg frame evm (.inRange (.sint width) expr) = .ok (.int i) := by
  have h0 : ¬ i < -(2^(width.val-1) : Int) := by omega
  have h1 : ¬ i ≥ (2^(width.val-1) : Int) := by omega
  simp only [evalExpr?, he, bind, EvalResult.bind, h0, h1, decide_false,
    Bool.or_self, Bool.false_eq_true, if_false, pure]

theorem signedNarrowRangeSourceOverflow {cfg frame evm expr i} (width : BitWidth)
    (he : evalExpr? cfg frame evm expr = .ok (.int i))
    (hhi : (2^(width.val-1) : Int) ≤ i) :
    evalExpr? cfg frame evm (.inRange (.sint width) expr) = .revert := by
  simp only [evalExpr?, he, bind, EvalResult.bind, hhi, decide_true, Bool.or_true, if_true]

theorem signedNarrowRangeSourceUnderflow {cfg frame evm expr i} (width : BitWidth)
    (he : evalExpr? cfg frame evm expr = .ok (.int i))
    (hlo : i < -(2^(width.val-1) : Int)) :
    evalExpr? cfg frame evm (.inRange (.sint width) expr) = .revert := by
  simp only [evalExpr?, he, bind, EvalResult.bind, hlo, decide_true, Bool.true_or, if_true]

end Benchmarks.CompoundIII.Comet

import Benchmarks.Midnight.OfferSourceValues
import Reasoning.SteleArithmetic

/-! Signed arithmetic used by the trade event's net credit change. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: subtracting two nonnegative signed words cannot increase the first.
theorem signedSubNonnegativeGuard {a b : UInt256}
    (ha : a.toNat < 2^255) (hb : b.toNat < 2^255) :
    UInt256.lor
      (UInt256.land (UInt256.isZero (UInt256.slt b ⟨0⟩))
        (UInt256.sgt (UInt256.sub a b) a))
      (UInt256.land (UInt256.slt b ⟨0⟩) (UInt256.slt (UInt256.sub a b) a)) = ⟨0⟩ := by
  have hb0 : UInt256.slt b ⟨0⟩ = ⟨0⟩ := slt_lit_zero (m := 0) (by decide) (by omega) hb
  have hgt : UInt256.sgt (UInt256.sub a b) a = ⟨0⟩ := by
    have hbool : UInt256.sgtBool (UInt256.sub a b) a = false := by
      unfold UInt256.sgtBool
      by_cases hle : b.toNat ≤ a.toNat
      · have hsub := usub_toNat hle
        rw [if_neg (by omega), if_neg (by omega)]
        exact decide_eq_false (show ¬ a < UInt256.sub a b by
          change ¬ a.toNat < (UInt256.sub a b).toNat
          omega)
      · have hsub := usub_toNat_underflow (Nat.lt_of_not_ge hle)
        rw [if_pos (by change 2^255 ≤ (UInt256.sub a b).toNat; change
          (UInt256.sub a b).toNat = 2^256 + a.toNat - b.toNat at hsub; omega),
          if_neg (by omega)]
    rw [UInt256.sgt, hbool]
    rfl
  rw [hb0, hgt]
  simp only [u256_land_zero_right, u256_land_zero_left]
  rfl

-- LIBRARY CANDIDATE: a uint word below the signed boundary casts without changing value.
theorem evalSignedWordCast {cfg : Config} {frame : Frame} {evm : State}
    {expr : Expr} {word : UInt256}
    (he : evalExpr? cfg frame evm expr = .ok (.int word.toNat))
    (hw : word.toNat < 2^255) :
    evalExpr? cfg frame evm (.cast expr (.elem (.int (.sint ⟨256, by decide⟩)))) =
      .ok (.int word.toNat) := by
  rw [evalExpr?, he]
  simp only [bind, EvalResult.bind, castValue?, EvalResult.ofOption]
  simpa only [Int.ofNat_eq_natCast] using congrArg (fun i ↦ EvalResult.ok (Value.int i))
    (normalizeInt_sint256_word_of_lt word hw)

def takeCreditDifferenceExpr : Expr :=
  .inRange (.sint ⟨256, by decide⟩) (.binary .sub
    (.cast (.var "buyerCreditIncrease") (.elem (.int (.sint ⟨256, by decide⟩))))
    (.cast (.var "sellerCreditDecrease") (.elem (.int (.sint ⟨256, by decide⟩)))))

theorem evalTakeCreditDifference {frame : Frame} {evm : State} {increase decrease : UInt256}
    (hi : frame.locals.get? "buyerCreditIncrease" = some (.int increase.toNat))
    (hd : frame.locals.get? "sellerCreditDecrease" = some (.int decrease.toNat))
    (hi128 : increase.toNat < 2^128) (hd128 : decrease.toNat < 2^128) :
    evalExpr? config frame evm takeCreditDifferenceExpr =
      .ok (.int ((increase.toNat : Int) - decrease.toNat)) := by
  have hei : evalExpr? config frame evm (.var "buyerCreditIncrease") =
      .ok (.int increase.toNat) := by simp only [evalExpr?, hi, EvalResult.ofOption]
  have hed : evalExpr? config frame evm (.var "sellerCreditDecrease") =
      .ok (.int decrease.toNat) := by simp only [evalExpr?, hd, EvalResult.ofOption]
  rw [takeCreditDifferenceExpr, evalExpr?,
    evalExpr_binary_nonshort (by decide) (by decide),
    evalSignedWordCast hei (by omega), evalSignedWordCast hed (by omega)]
  simp only [bind, EvalResult.bind, evalBinaryOp?]
  change (if (decide ((increase.toNat : Int) - decrease.toNat < -(2: Int)^255) ||
    decide ((increase.toNat : Int) - decrease.toNat ≥ (2: Int)^255)) = true then _ else _) = _
  rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)]
  rfl

end Benchmarks.Midnight

import Benchmarks.UniswapV4PoolManager.WordIntegerArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: unsigned word comparisons in arbitrary source expression contexts.
theorem evalWordLt {cfg : Config} {f : Frame} {evm : EVM.State} {ea eb : Expr} {a b : UInt256}
    (ha : evalExpr? cfg f evm ea = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg f evm eb = .ok (.int (Int.ofNat b.toNat))) :
    evalExpr? cfg f evm (.binary .lt ea eb) = .ok (.bool (decide (a.toNat < b.toNat))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
  simp only [bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast, Int.ofNat_lt]

theorem evalWordGt {cfg : Config} {f : Frame} {evm : EVM.State} {ea eb : Expr} {a b : UInt256}
    (ha : evalExpr? cfg f evm ea = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg f evm eb = .ok (.int (Int.ofNat b.toNat))) :
    evalExpr? cfg f evm (.binary .gt ea eb) = .ok (.bool (decide (b.toNat < a.toNat))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
  simp only [bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast, Int.ofNat_lt]

-- LIBRARY CANDIDATE: the common conditional integer representation of a Boolean.
theorem evalBoolWord {cfg : Config} {f : Frame} {evm : EVM.State} {e : Expr} {b : Bool}
    (he : evalExpr? cfg f evm e = .ok (.bool b)) :
    evalExpr? cfg f evm (.ite e (.intLit 1) (.intLit 0)) =
      .ok (.int (Int.ofNat (UInt256.fromBool b).toNat)) := by
  cases b <;> simp only [evalExpr?, he, bind, EvalResult.bind, pure] <;> rfl

-- LIBRARY CANDIDATE: one outer uint256 cast can normalize a chain of subtractions.
theorem evalWordSubSub {cfg : Config} {f : Frame} {evm : EVM.State} {ea eb ec : Expr} {a b c : UInt256}
    (ha : evalExpr? cfg f evm ea = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg f evm eb = .ok (.int (Int.ofNat b.toNat)))
    (hc : evalExpr? cfg f evm ec = .ok (.int (Int.ofNat c.toNat))) :
    evalExpr? cfg f evm (.cast (.binary .sub (.binary .sub ea eb) ec) (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat (UInt256.sub (UInt256.sub a b) c).toNat)) := by
  have hab : evalExpr? cfg f evm (.binary .sub ea eb) = .ok (.int (Int.ofNat a.toNat - Int.ofNat b.toNat)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
    rfl
  have he : evalExpr? cfg f evm (.binary .sub (.binary .sub ea eb) ec) =
      .ok (.int (Int.ofNat a.toNat - Int.ofNat b.toNat - Int.ofNat c.toNat)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hab, hc]
    rfl
  have hw : EVM.wordOfInt (Int.ofNat a.toNat - Int.ofNat b.toNat - Int.ofNat c.toNat) =
      UInt256.sub (UInt256.sub a b) c := by
    rw [wordOfIntSub, wordOfInt_sub_natCasts, wordOfInt_ofNat_toNat]
  have hn : normalizeInt (.uint ⟨256, by decide⟩)
      (Int.ofNat a.toNat - Int.ofNat b.toNat - Int.ofNat c.toNat) =
      Int.ofNat (UInt256.sub (UInt256.sub a b) c).toNat := by
    change (_ % (2^256 : Int)) = _
    rw [← wordOfIntResidue, hw]
  simpa only [hn] using evalExpr_cast_int (intType := .uint ⟨256, by decide⟩) he

end Benchmarks.UniswapV4PoolManager

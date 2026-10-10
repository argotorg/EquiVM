import Benchmarks.UniswapV4PoolManager.WordOperationsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: unsigned right shift also handles oversized word-valued shift amounts.
theorem evalWordShrWord {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (hx : evalExpr? cfg f evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg f evm b = .ok (.int (Int.ofNat y.toNat))) :
    evalExpr? cfg f evm (.binary (.shr (.uint ⟨256, by decide⟩)) a b) =
      .ok (.int (Int.ofNat (UInt256.shiftRight x y).toNat)) := by
  by_cases hn : y.toNat < 256
  · simpa only [u256_ofNat_toNat] using evalWordShr hn hx hy
  · rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
    simp only [bind, EvalResult.bind, evalBinaryOp?, IntType.bitWidth,
      Int.ofNat_eq_natCast, Int.not_lt.mpr (Int.natCast_nonneg y.toNat),
      Int.toNat_natCast, if_false, Nat.le_of_not_gt hn, if_true, IntType.isSigned,
      Bool.false_and, Bool.false_eq_true]
    rw [UInt256.shiftRight, if_pos (show y.val ≥ 256 from Nat.le_of_not_gt hn)]
    rfl

-- LIBRARY CANDIDATE: a shifted comparison word selects a power of two.
theorem shiftComparison_toNat (a b : UInt256) {n : Nat} (hn : n < 256) :
    (UInt256.shiftLeft (UInt256.lt a b) (UInt256.ofNat n)).toNat =
      if a.toNat < b.toNat then 2^n else 0 := by
  have hpow : 2^n < UInt256.size := by
    change 2^n < 2^256
    exact Nat.pow_lt_pow_right (by decide) hn
  by_cases h : a.toNat < b.toNat
  · rw [if_pos h, ult_one h, wordShiftLeftNat _ hn]
    change (1*2^n)%UInt256.size = 2^n
    rw [Nat.one_mul, Nat.mod_eq_of_lt hpow]
  · rw [if_neg h, ult_zero (Nat.le_of_not_gt h), wordShiftLeftNat _ hn]
    change (0*2^n)%UInt256.size = 0
    simp only [Nat.zero_mul, Nat.zero_mod]

-- LIBRARY CANDIDATE: source ternary selection implemented with LT followed by SHL.
theorem evalComparisonPower {cfg : Config} {f : Frame} {evm : EVM.State}
    {a b : Expr} {x limit : UInt256} {bit : Nat} (hbit : bit < 256)
    (hx : evalExpr? cfg f evm a = .ok (.int (Int.ofNat x.toNat)))
    (hl : evalExpr? cfg f evm b = .ok (.int (Int.ofNat limit.toNat))) :
    evalExpr? cfg f evm (.ite (.binary .gt a b) (.intLit (Int.ofNat (2^bit))) (.intLit 0)) =
      .ok (.int (Int.ofNat (UInt256.shiftLeft (UInt256.lt limit x) (UInt256.ofNat bit)).toNat)) := by
  have hc : evalExpr? cfg f evm (.binary .gt a b) = .ok (.bool (decide (limit.toNat < x.toNat))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hl]
    simp only [bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast, Nat.cast_lt]
  rw [evalExpr?, hc, shiftComparison_toNat _ _ hbit]
  by_cases ht : limit.toNat < x.toNat
  · simp only [ht, decide_true, if_true, bind, EvalResult.bind, evalExpr?, pure]
  · simp only [ht, decide_false, if_false, bind, EvalResult.bind, evalExpr?, pure]
    rfl

end Benchmarks.UniswapV4PoolManager

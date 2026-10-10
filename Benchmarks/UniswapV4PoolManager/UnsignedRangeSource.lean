import Benchmarks.UniswapV4PoolManager.Values

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES Reasoning.Theory.uint256RangeSourceOk/Overflow to any width and integer input.
def unsignedFits (bits : BitWidth) (n : Int) : Prop := 0 ≤ n ∧ n < (2 : Int)^bits.val
instance (bits : BitWidth) (n : Int) : Decidable (unsignedFits bits n) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem evalUnsignedRange {cfg : Config} {f : Frame} {evm : EVM.State} {e : Expr} {n : Int}
    (bits : BitWidth) (he : evalExpr? cfg f evm e = .ok (.int n)) :
    evalExpr? cfg f evm (.inRange (.uint bits) e) =
      if unsignedFits bits n then .ok (.int n) else .revert := by
  simp only [evalExpr?, he, bind, EvalResult.bind]
  by_cases h : unsignedFits bits n
  · rw [if_pos h]
    have hl : ¬n < 0 := by have := h.1; omega
    have hh : ¬n ≥ (2 : Int)^bits.val := by have := h.2; omega
    simp only [hl, hh, decide_false, Bool.false_or, Bool.false_eq_true, if_false, pure]
  · rw [if_neg h, if_pos]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    unfold unsignedFits at h
    omega

end Benchmarks.UniswapV4PoolManager

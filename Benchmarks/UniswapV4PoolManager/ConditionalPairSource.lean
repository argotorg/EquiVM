import Benchmarks.UniswapV4PoolManager.ConditionalSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: compose two pure rejection guards into one conjunction.
theorem execBlock_rejectUnlessPair {cfg : Config} {f : Frame} {evm : State}
    {a b : Expr} {p q : Prop} [Decidable p] [Decidable q]
    (ha : evalExpr? cfg f evm a = .ok (.bool (decide (¬p))))
    (hb : evalExpr? cfg f evm b = .ok (.bool (decide (¬q)))) :
    ExecBlock cfg f evm [.ite a [.require (.boolLit false)] [], .ite b [.require (.boolLit false)] []]
      (if p ∧ q then .ok f evm else .reverted) := by
  have h0 := execStmt_rejectIf ha
  have h1 := execStmt_rejectIf hb
  by_cases hp : p
  · simp only [hp, not_true_eq_false, decide_false, Bool.false_eq_true, if_false] at h0
    by_cases hq : q
    · simp only [hq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false] at h1
      rw [if_pos ⟨hp, hq⟩]
      exact ExecBlock.consNormal h0 (execBlock_singleton h1)
    · simp only [decide_eq_true hq, if_true] at h1
      rw [if_neg (fun hh => hq hh.2)]
      exact ExecBlock.consNormal h0 (ExecBlock.consRevert h1)
  · simp only [decide_eq_true hp, if_true] at h0
    rw [if_neg (fun hh => hp hh.1)]
    exact ExecBlock.consRevert h0

end Benchmarks.UniswapV4PoolManager

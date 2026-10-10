import Benchmarks.UniswapV4PoolManager.SignedDivisionSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES tickSpacingMin_eval to arbitrary expressions and signed operands.
-- LIBRARY CANDIDATE: signed quotient with the source's negative-remainder correction.
theorem evalSignedQuotientCorrection {cfg : Config} {f : Frame} {evm : EVM.State}
    {a b : Expr} {x y : Int}
    (hx : evalExpr? cfg f evm a = .ok (.int x)) (hy : evalExpr? cfg f evm b = .ok (.int y))
    (hn : y ≠ 0) :
    evalExpr? cfg f evm (.binary .sub (.binary .sdiv a b)
      (.ite (.binary .lt (.binary .srem a b) (.intLit 0)) (.intLit 1) (.intLit 0))) =
      .ok (.int (x.tdiv y - if x.tmod y < 0 then 1 else 0)) := by
  have hd := evalSignedDiv hx hy hn
  have hr := evalSignedRem hx hy hn
  have hlt : evalExpr? cfg f evm (.binary .lt (.binary .srem a b) (.intLit 0)) =
      .ok (.bool (decide (x.tmod y < 0))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hr]
    simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?]
  rw [evalExpr_binary_nonshort (by decide) (by decide), hd, evalExpr?, hlt]
  by_cases hr0 : x.tmod y < 0 <;>
    simp only [hr0, decide_true, decide_false, if_true, if_false,
      bind, EvalResult.bind, evalExpr?, pure, evalBinaryOp?]

end Benchmarks.UniswapV4PoolManager

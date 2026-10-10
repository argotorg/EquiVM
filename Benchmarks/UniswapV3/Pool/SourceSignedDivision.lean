import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATES: signed division and comparisons in arbitrary source frames.
theorem evalExpr_int_sdiv {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : Int}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int a))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int b)) (hn : b ≠ 0) :
    evalExpr? cfg frame evm (.binary .sdiv lhs rhs) = .ok (.int (a.tdiv b)) := by
  simp only [evalExpr?, ha, hb, evalBinaryOp?, hn, if_false, bind, EvalResult.bind]

theorem evalExpr_int_srem {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : Int}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int a))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int b)) (hn : b ≠ 0) :
    evalExpr? cfg frame evm (.binary .srem lhs rhs) = .ok (.int (a.tmod b)) := by
  simp only [evalExpr?, ha, hb, evalBinaryOp?, hn, if_false, bind, EvalResult.bind]

theorem evalExpr_int_ne {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : Int}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int a))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int b)) :
    evalExpr? cfg frame evm (.binary .ne lhs rhs) = .ok (.bool (decide (a ≠ b))) := by
  simp only [evalExpr?, ha, hb, evalBinaryOp?, bind, EvalResult.bind]
  congr 2
  have he : (Value.int a == Value.int b) = decide (a = b) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, Value.int.injEq]
  rw [he]
  simp only [ne_eq, decide_not]

theorem evalExpr_int_lt {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : Int}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int a))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int b)) :
    evalExpr? cfg frame evm (.binary .lt lhs rhs) = .ok (.bool (decide (a < b))) := by
  simp only [evalExpr?, ha, hb, evalBinaryOp?, bind, EvalResult.bind]

end Benchmarks.UniswapV3.Pool

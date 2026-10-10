import Benchmarks.UniswapV4PoolManager.Values

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: boolean conditional expressions in arbitrary frames.
theorem evalBoolIte {cfg : Config} {f : Frame} {evm : EVM.State} {cond yes no : Expr} {c a b : Bool}
    (hc : evalExpr? cfg f evm cond = .ok (.bool c))
    (ha : evalExpr? cfg f evm yes = .ok (.bool a))
    (hb : evalExpr? cfg f evm no = .ok (.bool b)) :
    evalExpr? cfg f evm (.ite cond yes no) = .ok (.bool (if c then a else b)) := by
  cases c <;> simp only [evalExpr?, hc, bind, EvalResult.bind, ha, hb, Bool.false_eq_true, if_false, if_true]

-- LIBRARY CANDIDATE: an early false return preceding a boolean-returning block.
theorem falseReturnGuard {cfg : Config} {f : Frame} {evm : EVM.State} {cond : Expr} {rest : List Stmt} {c result : Bool}
    (hc : evalExpr? cfg f evm cond = .ok (.bool c))
    (hr : ExecBlock cfg f evm rest (.returned f evm (some [.bool result]))) :
    ExecBlock cfg f evm (.ite cond [.return [.boolLit false]] [] :: rest)
      (.returned f evm (some [.bool (if c then false else result)])) := by
  cases c with
  | false => exact ExecBlock.consNormal (ExecStmt.iteFalse hc ExecBlock.nil) hr
  | true =>
    simp only [if_true]
    exact ExecBlock.consReturn (ExecStmt.iteTrue hc (ABlock.start.returns (by simp only [evalExpr?, pure])))

end Benchmarks.UniswapV4PoolManager

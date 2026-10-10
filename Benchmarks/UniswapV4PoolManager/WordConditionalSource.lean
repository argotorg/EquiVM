import Benchmarks.UniswapV4PoolManager.WordLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: a word-valued conditional expression with a proved source condition.
theorem evalWordConditional {cfg : Config} {f : Frame} {evm : EVM.State} {test yes no : Expr}
    {p : Prop} [Decidable p] {x y : UInt256}
    (hc : evalExpr? cfg f evm test = .ok (.bool (decide p)))
    (hx : evalExpr? cfg f evm yes = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg f evm no = .ok (.int (Int.ofNat y.toNat))) :
    evalExpr? cfg f evm (.ite test yes no) = .ok (.int (Int.ofNat (if p then x else y).toNat)) := by
  by_cases hp : p
  · simp only [evalExpr?, hc, decide_eq_true hp, bind, EvalResult.bind, if_true, hx, if_pos hp]
  · simp only [evalExpr?, hc, decide_eq_false hp, bind, EvalResult.bind, Bool.false_eq_true, if_false, hy, if_neg hp]

end Benchmarks.UniswapV4PoolManager

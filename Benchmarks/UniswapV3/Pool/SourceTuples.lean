import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: projecting a component of an evaluated tuple.
theorem evalExpr_tupleGet {cfg : Config} {frame : Frame} {evm : EVM.State}
    {e : Expr} {values : List Value} {value : Value} {i : Nat}
    (he : evalExpr? cfg frame evm e = .ok (.tuple values))
    (hi : values[i]? = some value) :
    evalExpr? cfg frame evm (.tupleGet e i) = .ok value := by
  simp only [evalExpr?, he, bind, EvalResult.bind, tupleGetValue?, hi]

end Benchmarks.UniswapV3.Pool

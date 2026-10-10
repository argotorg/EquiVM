import Benchmarks.UniswapV3.Pool.SourceWordArithmetic
import Benchmarks.UniswapV3.Pool.ArrayStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: zero-denominator remainder in arbitrary source frames.
theorem evalExpr_int_mod_zero {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a : Int}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int a))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int 0)) :
    evalExpr? cfg frame evm (.binary .mod lhs rhs) = .revert := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, ↓reduceIte]

-- LIBRARY CANDIDATE: propagate failure while evaluating an array index.
theorem evalStorageRef_aindex_eval_revert {cfg : Config} {frame : Frame} {evm : EVM.State}
    {base : Ident} {index : Expr} (he : evalExpr? cfg frame evm index = .revert) :
    evalStorageRef cfg frame evm ⟨base, [.aindex index]⟩ = .revert := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, he, bind, EvalResult.bind]

end Benchmarks.UniswapV3.Pool

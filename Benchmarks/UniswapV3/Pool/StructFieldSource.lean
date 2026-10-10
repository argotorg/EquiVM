import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: a pure struct field can be evaluated from its base and field lookup.
theorem evalExpr_structField {cfg : Config} {frame : Frame} {evm : EVM.State}
    {base : Expr} {tag name : Ident} {fields : List (Ident × Value)} {value : Value}
    (hbase : evalExpr? cfg frame evm base = .ok (.struct tag fields))
    (hfield : lookupAssoc fields name = some value) :
    evalExpr? cfg frame evm (.field base name) = .ok value := by
  simp only [evalExpr?, hbase, bind, EvalResult.bind, lookupField?, hfield, EvalResult.ofOption]

end Benchmarks.UniswapV3.Pool

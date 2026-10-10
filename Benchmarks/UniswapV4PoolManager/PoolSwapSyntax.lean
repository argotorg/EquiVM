import Benchmarks.UniswapV4PoolManager.Spec

open Solm
namespace Benchmarks.UniswapV4PoolManager

abbrev poolSwapFunction : FunctionDecl := contract.functions[76]!

def poolSwapLoopBody : List Stmt :=
  match poolSwapFunction.body[28]! with
  | .while _ body => body
  | _ => []

end Benchmarks.UniswapV4PoolManager

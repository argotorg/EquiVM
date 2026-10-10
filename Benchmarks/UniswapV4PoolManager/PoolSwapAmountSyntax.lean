import Benchmarks.UniswapV4PoolManager.PoolSwapSyntax

open Solm ABI
namespace Benchmarks.UniswapV4PoolManager

def poolSwapInputAmountStmts : List Stmt :=
  match poolSwapLoopBody[15]! with | .ite _ _ stmts => stmts | _ => []
def poolSwapOutputAmountStmts : List Stmt :=
  match poolSwapLoopBody[15]! with | .ite _ stmts _ => stmts | _ => []

theorem poolSwapLoop_amounts : poolSwapLoopBody[15]! =
    .ite (.binary .gt (.field (.var "params") "amountSpecified") (.intLit 0))
      poolSwapOutputAmountStmts poolSwapInputAmountStmts := rfl

end Benchmarks.UniswapV4PoolManager

import Benchmarks.UniswapV4PoolManager.PoolSwapSyntax

open Solm
namespace Benchmarks.UniswapV4PoolManager

def poolSwapCrossStmts : List Stmt :=
  match poolSwapLoopBody[18]! with
  | .ite _ (.ite _ body _ :: _) _ => body
  | _ => []

def poolSwapCrossAlias : Ident :=
  match poolSwapCrossStmts[2]! with
  | .letStorage name _ => name
  | _ => ""

def poolSwapBoundaryTickStmt : Stmt :=
  match poolSwapLoopBody[18]! with
  | .ite _ (_ :: stmt :: _) _ => stmt
  | _ => .require (.boolLit false)

def poolSwapRepriceStmt : Stmt :=
  match poolSwapLoopBody[18]! with
  | .ite _ _ (stmt :: _) => stmt
  | _ => .require (.boolLit false)

theorem poolSwapLoop_tick : poolSwapLoopBody[18]! =
    .ite (.binary .eq (.field (.var "result") "sqrtPriceX96") (.field (.var "step") "sqrtPriceNextX96"))
      [.ite (.field (.var "step") "initialized") poolSwapCrossStmts [], poolSwapBoundaryTickStmt]
      [poolSwapRepriceStmt] := rfl

end Benchmarks.UniswapV4PoolManager

import Benchmarks.UniswapV4PoolManager.PoolSwapSyntax

open Solm
namespace Benchmarks.UniswapV4PoolManager

def poolSwapBitmapAlias : Ident :=
  match poolSwapLoopBody[1]! with
  | .letStorage name _ => name
  | _ => ""

theorem poolSwapLoop_scan : poolSwapLoopBody.take 5 =
    [.assign .localVar {base := "step", steps := [.field "sqrtPriceStartX96"]}
      (.field (.var "result") "sqrtPriceX96"),
     .letStorage poolSwapBitmapAlias {base := "self", steps := [.field "tickBitmap"]},
     .internalCall "TickBitmap_nextInitializedTickWithinOneWord"
       [.var poolSwapBitmapAlias, .field (.var "result") "tick", .field (.var "params") "tickSpacing", .var "zeroForOne"] "__c12",
     .assign .localVar {base := "step", steps := [.field "tickNext"]} (.tupleGet (.var "__c12") 0),
     .assign .localVar {base := "step", steps := [.field "initialized"]} (.tupleGet (.var "__c12") 1)] := rfl

end Benchmarks.UniswapV4PoolManager

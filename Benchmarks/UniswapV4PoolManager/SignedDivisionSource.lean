import Benchmarks.UniswapV4PoolManager.SignedWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: source signed division in an arbitrary expression context.
theorem evalSignedDiv {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x y : Int}
    (hx : evalExpr? cfg f evm a = .ok (.int x)) (hy : evalExpr? cfg f evm b = .ok (.int y))
    (hn : y ≠ 0) :
    evalExpr? cfg f evm (.binary .sdiv a b) = .ok (.int (x.tdiv y)) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
  simp only [bind, EvalResult.bind, evalBinaryOp?, if_neg hn]

-- LIBRARY CANDIDATE: source signed remainder in an arbitrary expression context.
theorem evalSignedRem {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x y : Int}
    (hx : evalExpr? cfg f evm a = .ok (.int x)) (hy : evalExpr? cfg f evm b = .ok (.int y))
    (hn : y ≠ 0) :
    evalExpr? cfg f evm (.binary .srem a b) = .ok (.int (x.tmod y)) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
  simp only [bind, EvalResult.bind, evalBinaryOp?, if_neg hn]

end Benchmarks.UniswapV4PoolManager

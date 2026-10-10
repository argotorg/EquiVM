import Benchmarks.UniswapV4PoolManager.LPFeeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: compare arbitrary natural-valued expressions with >=.
theorem evalNatGe {cfg : Config} {f : Frame} {evm : State} {e0 e1 : Expr} {a b : Nat}
    (h0 : evalExpr? cfg f evm e0 = .ok (.int (Int.ofNat a)))
    (h1 : evalExpr? cfg f evm e1 = .ok (.int (Int.ofNat b))) :
    evalExpr? cfg f evm (.binary .ge e0 e1) = .ok (.bool (decide (b ≤ a))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), h0, h1]
  simp only [bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast, Nat.cast_le]

end Benchmarks.UniswapV4PoolManager

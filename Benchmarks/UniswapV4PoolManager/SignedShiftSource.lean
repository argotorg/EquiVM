import Benchmarks.UniswapV4PoolManager.WordSar

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: bounded signed right shift at an arbitrary integer width.
theorem evalSignedShr {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr}
    {x : Int} {n : Nat} (bits : BitWidth) (hn : n < bits.val)
    (hx : evalExpr? cfg f evm a = .ok (.int x))
    (hy : evalExpr? cfg f evm b = .ok (.int (Int.ofNat n))) :
    evalExpr? cfg f evm (.binary (.shr (.sint bits)) a b) =
      .ok (.int (normalizeInt (.sint bits) x / Int.ofNat (2^n))) := by
  rw [evalExpr_binary_nonshort (by intro h; cases h) (by intro h; cases h), hx, hy]
  simp only [bind, EvalResult.bind, evalBinaryOp?, IntType.bitWidth, Int.ofNat_eq_natCast,
    Int.not_lt.mpr (Int.natCast_nonneg n), if_false, Int.toNat_natCast, Nat.not_le.mpr hn]
  rfl

end Benchmarks.UniswapV4PoolManager

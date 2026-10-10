import Benchmarks.UniswapV4PoolManager.WordOperationsSource
import Benchmarks.UniswapV4PoolManager.SignedRemainderWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES Reasoning.Theory.evalExpr_mod_int_ok to arbitrary word-valued expressions and frames.
theorem evalWordMod {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (hx : evalExpr? cfg f evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg f evm b = .ok (.int (Int.ofNat y.toNat))) (hn : y ≠ ⟨0⟩) :
    evalExpr? cfg f evm (.binary .mod a b) = .ok (.int (Int.ofNat (UInt256.mod x y).toNat)) := by
  have hz : y.toNat ≠ 0 := fun h => hn (uint256_toNat_eq_zero h)
  rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
  simp only [bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast,
    Int.natCast_eq_zero, hz, if_false, wordMod_toNat hz, Int.natCast_emod]

end Benchmarks.UniswapV4PoolManager

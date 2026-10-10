import Benchmarks.UniswapV4PoolManager.WordOperationsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: unsigned bitwise complement in an arbitrary source expression.
theorem evalWordNot {cfg : Config} {f : Frame} {evm : EVM.State} {e : Expr} {w : UInt256}
    (he : evalExpr? cfg f evm e = .ok (.int (Int.ofNat w.toNat))) :
    evalExpr? cfg f evm (.unary (.bitNot (.uint ⟨256, by decide⟩)) e) =
      .ok (.int (Int.ofNat (UInt256.lnot w).toNat)) := by
  rw [evalExpr?, he]
  simp only [bind, EvalResult.bind, evalUnaryOp?, IntType.bitWidth, normalizeInt_uint256_word,
    EVM.twoPow, EvalResult.ofOption]
  change EvalResult.ok (Value.int (normalizeInt (.uint ⟨256, by decide⟩)
    (Int.ofNat (2^256-1-w.toNat)))) = _
  rw [← lnot_toNat_gen, normalizeInt_uint256_word]

end Benchmarks.UniswapV4PoolManager

import Benchmarks.UniswapV4PoolManager.Slot0Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: word XOR has its natural bitwise value without truncation.
theorem wordXor_toNat (x y : UInt256) : (UInt256.xor x y).toNat = Nat.xor x.toNat y.toNat := by
  change Nat.xor x.toNat y.toNat % UInt256.size = _
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 256) x.val.isLt y.val.isLt)

-- LIBRARY CANDIDATE: word XOR in arbitrary source expression contexts.
theorem evalWordXor {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (hx : evalExpr? cfg f evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg f evm b = .ok (.int (Int.ofNat y.toNat))) :
    evalExpr? cfg f evm (.binary (.bitXor (.uint ⟨256, by decide⟩)) a b) =
      .ok (.int (Int.ofNat (UInt256.xor x y).toNat)) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
  simp only [bind, EvalResult.bind, evalBinaryOp?, evalIntBitwise, IntType.bitWidth,
    normalizeInt_uint256_word]
  change EvalResult.ok (Value.int (normalizeInt (.uint ⟨256, by decide⟩)
    (Int.ofNat (Nat.xor x.toNat y.toNat)))) = _
  rw [← wordXor_toNat, normalizeInt_uint256_word]

end Benchmarks.UniswapV4PoolManager

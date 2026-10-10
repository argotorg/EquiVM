import Benchmarks.UniswapV3.Pool.ModularWords
import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: natural interpretation of bitwise XOR on EVM words.
theorem wordXor_toNat (a b : UInt256) :
    (UInt256.xor a b).toNat = a.toNat ^^^ b.toNat := by
  change (a.toNat ^^^ b.toNat) % UInt256.size = _
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 256) a.val.isLt b.val.isLt)

-- LIBRARY CANDIDATE: source unsigned XOR agrees with the corresponding EVM word operation.
theorem evalExpr_word_xor {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b.toNat))) :
    evalExpr? cfg frame evm (.binary (.bitXor (.uint ⟨256, by decide⟩)) lhs rhs) =
      .ok (.int (Int.ofNat (UInt256.xor a b).toNat)) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, evalIntBitwise,
    IntType.bitWidth, normalizeInt_uint256_word]
  change EvalResult.ok (Value.int (normalizeInt (.uint ⟨256, by decide⟩)
    (Int.ofNat (a.toNat ^^^ b.toNat)))) = _
  rw [← wordXor_toNat, normalizeInt_uint256_word]

end Benchmarks.UniswapV3.Pool

import Benchmarks.UniswapV4PoolManager.WordOperationsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES Reasoning.Theory.naturalAddSource to a bounded EVM word result.
theorem evalBoundedWordAdd {cfg : Config} {f : Frame} {evm : State} {a b : Expr} {x y : UInt256}
    (hx : evalExpr? cfg f evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg f evm b = .ok (.int (Int.ofNat y.toNat)))
    (hbound : x.toNat+y.toNat < UInt256.size) :
    evalExpr? cfg f evm (.binary .add a b) = .ok (.int (Int.ofNat (x+y).toNat)) := by
  rw [uadd_toNat, Nat.mod_eq_of_lt hbound]
  exact naturalAddSource hx hy

-- LIBRARY CANDIDATE: uncast source multiplication agrees with a bounded word product.
theorem evalBoundedWordMul {cfg : Config} {f : Frame} {evm : State} {a b : Expr} {x y : UInt256}
    (hx : evalExpr? cfg f evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg f evm b = .ok (.int (Int.ofNat y.toNat)))
    (hbound : x.toNat*y.toNat < UInt256.size) :
    evalExpr? cfg f evm (.binary .mul a b) = .ok (.int (Int.ofNat (UInt256.mul x y).toNat)) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
  simp only [bind, EvalResult.bind, evalBinaryOp?]
  rw [show (UInt256.mul x y).toNat = x.toNat*y.toNat from umul_toNat x y hbound]
  rfl

end Benchmarks.UniswapV4PoolManager

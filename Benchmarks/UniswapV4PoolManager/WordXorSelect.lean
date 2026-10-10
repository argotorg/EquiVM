import Benchmarks.UniswapV4PoolManager.WordXorSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: multiplication by the word one.
theorem wordMulOneRight (x : UInt256) : UInt256.mul x ⟨1⟩ = x := by
  apply u256_inj
  rw [u256_mul_toNat]
  change (x.toNat * 1) % UInt256.size = x.toNat
  rw [Nat.mul_one]
  exact Nat.mod_eq_of_lt x.val.isLt

-- LIBRARY CANDIDATE: the XOR/MUL conditional selection used by optimized bytecode.
theorem wordXorSelect (x y : UInt256) (pickX : Bool) :
    UInt256.xor (UInt256.mul (UInt256.xor x y) (if pickX then ⟨1⟩ else ⟨0⟩)) y =
      if pickX then x else y := by
  cases pickX with
  | false =>
    simp only [Bool.false_eq_true, if_false, u256_mul_zero]
    apply u256_inj
    rw [wordXor_toNat]
    exact Nat.zero_xor _
  | true =>
    simp only [if_true, wordMulOneRight]
    apply u256_inj
    rw [wordXor_toNat, wordXor_toNat]
    exact Nat.xor_xor_cancel_right x.toNat y.toNat

end Benchmarks.UniswapV4PoolManager

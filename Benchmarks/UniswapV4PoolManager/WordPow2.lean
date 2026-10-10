import Benchmarks.UniswapV4PoolManager.WordOperationsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: multiplication by the word one.
theorem wordMulOne (x : UInt256) : UInt256.mul x ⟨1⟩ = x := by
  apply u256_inj
  rw [u256_mul_toNat]
  change (x.toNat * 1) % UInt256.size = x.toNat
  rw [Nat.mul_one]
  exact Nat.mod_eq_of_lt x.val.isLt

-- LIBRARY CANDIDATE: division and multiplication by a word-sized power of two are shifts.
theorem wordDivPow2 (x : UInt256) {n : Nat} (hn : n < 256) :
    UInt256.div x (UInt256.ofNat (2^n)) = UInt256.shiftRight x (UInt256.ofNat n) := by
  apply u256_inj
  rw [udiv_toNat, UInt256.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide) hn),
    wordShiftRightNat x hn]

theorem wordMulPow2 (x : UInt256) {n : Nat} (hn : n < 256) :
    UInt256.mul x (UInt256.ofNat (2^n)) = UInt256.shiftLeft x (UInt256.ofNat n) := by
  apply u256_inj
  rw [u256_mul_toNat, UInt256.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide) hn),
    wordShiftLeftNat x hn]

end Benchmarks.UniswapV4PoolManager

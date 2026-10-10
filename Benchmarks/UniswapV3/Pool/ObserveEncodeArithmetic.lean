import Benchmarks.UniswapV3.Pool.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATES: arithmetic on natural literals in EVM words.
theorem wordNat_add (a b : Nat) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  apply u256_inj
  simp only [uadd_toNat, ofNat_toNat_mod, Nat.add_mod_mod, Nat.mod_add_mod]

theorem wordNat_mul (a b : Nat) :
    UInt256.mul (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a * b) := by
  apply u256_inj
  simp only [u256_mul_toNat, ofNat_toNat_mod, Nat.mul_mod_mod, Nat.mod_mul_mod]

theorem wordAddNat_assoc (p : UInt256) (a b : Nat) :
    (p + UInt256.ofNat a) + UInt256.ofNat b = p + UInt256.ofNat (a + b) := by
  rw [u256_add_assoc, wordNat_add]

theorem wordAddNat_left_assoc (p : UInt256) (a b : Nat) :
    UInt256.ofNat a + (UInt256.ofNat b + p) = p + UInt256.ofNat (a + b) := by
  rw [← u256_add_assoc, wordNat_add, u256_add_comm]

end Benchmarks.UniswapV3.Pool

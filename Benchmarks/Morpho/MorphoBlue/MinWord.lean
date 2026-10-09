import Benchmarks.Morpho.MorphoBlue.MinSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: exact natural value of the word xor operation.
theorem wordXor_toNat (x y : UInt256) :
    (UInt256.xor x y).toNat = x.toNat ^^^ y.toNat := by
  change (x.toNat ^^^ y.toNat) % UInt256.size = _
  apply Nat.mod_eq_of_lt
  exact Nat.xor_lt_two_pow (n := 256) x.val.isLt y.val.isLt

-- LIBRARY CANDIDATE: multiplication by a word containing one.
theorem wordMul_one_left (x : UInt256) : UInt256.mul (⟨1⟩ : UInt256) x = x := by
  apply u256_inj
  rw [u256_mul_toNat]
  change (1 * x.toNat) % UInt256.size = _
  rw [Nat.one_mul]
  exact Nat.mod_eq_of_lt x.val.isLt

-- LIBRARY CANDIDATE: the via-IR branchless unsigned minimum.
theorem minWord_evm (x y : UInt256) :
    UInt256.xor x (UInt256.mul (UInt256.gt x y) (UInt256.xor x y)) = minWord x y := by
  by_cases h : y.toNat < x.toNat
  · rw [ugt_one h, wordMul_one_left, minWord, if_neg (by omega)]
    apply u256_inj
    rw [wordXor_toNat, wordXor_toNat, Nat.xor_xor_cancel_left]
  · rw [ugt_zero (Nat.le_of_not_gt h), u256_mul_zero_left]
    have hx : UInt256.xor x ⟨0⟩ = x := by
      apply u256_inj
      rw [wordXor_toNat]
      exact Nat.xor_zero x.toNat
    rw [hx, minWord]
    split
    · rfl
    · apply u256_inj; omega

theorem minWord_evm_alt (x y : UInt256) :
    UInt256.xor (UInt256.mul (UInt256.xor x y) (UInt256.lt y x)) x = minWord x y := by
  have hc : UInt256.lt y x = UInt256.gt x y := rfl
  rw [hc, u256_mul_comm]
  have hx (a b : UInt256) : UInt256.xor a b = UInt256.xor b a := by
    apply u256_inj
    rw [wordXor_toNat, wordXor_toNat, Nat.xor_comm]
  rw [hx]
  exact minWord_evm x y

end Benchmarks.Morpho.MorphoBlue

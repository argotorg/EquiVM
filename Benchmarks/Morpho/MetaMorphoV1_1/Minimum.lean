import Reasoning.WordArithmetic

/-! The branchless unsigned minimum used by the withdrawal calculation. -/

open Ethereum Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def minimumWord (x y : UInt256) : UInt256 := if x.toNat < y.toNat then x else y

-- LIBRARY CANDIDATE: xor-selected unsigned minimum.
theorem branchlessMinimum (x y : UInt256) :
    UInt256.xor (UInt256.mul (UInt256.xor y x) (UInt256.lt x y)) y = minimumWord x y := by
  have hmul (a : UInt256) : UInt256.mul a ⟨1⟩ = a := by
    apply u256_inj
    simp [UInt256.mul, UInt256.toNat]
  have hcancel : UInt256.xor (UInt256.xor y x) y = x := by
    apply u256_inj
    have hbound : y.toNat ^^^ x.toNat < UInt256.size :=
      Nat.xor_lt_two_pow (n := 256) y.val.isLt x.val.isLt
    change ((y.toNat ^^^ x.toNat) % UInt256.size ^^^ y.toNat) % UInt256.size = x.toNat
    rw [Nat.mod_eq_of_lt hbound, Nat.xor_comm y.toNat x.toNat,
      Nat.xor_xor_cancel_right]
    exact Nat.mod_eq_of_lt x.val.isLt
  have hzero : UInt256.xor ⟨0⟩ y = y := by
    apply u256_inj
    change (0 ^^^ y.toNat) % UInt256.size = y.toNat
    rw [Nat.zero_xor]
    exact Nat.mod_eq_of_lt y.val.isLt
  by_cases hxy : x.toNat < y.toNat
  · rw [ult_one hxy, hmul, hcancel, minimumWord, if_pos hxy]
  · rw [ult_zero (Nat.le_of_not_gt hxy), u256_mul_zero_right, hzero,
      minimumWord, if_neg hxy]

theorem minimumWord_toNat (x y : UInt256) :
    (minimumWord x y).toNat = min x.toNat y.toNat := by
  unfold minimumWord
  split_ifs with h
  · exact (Nat.min_eq_left (Nat.le_of_lt h)).symm
  · exact (Nat.min_eq_right (Nat.le_of_not_gt h)).symm

theorem minimumWord_comm (x y : UInt256) : minimumWord x y = minimumWord y x := by
  apply u256_inj
  rw [minimumWord_toNat, minimumWord_toNat, Nat.min_comm]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

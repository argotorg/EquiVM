import Benchmarks.Morpho.MetaMorphoV1_1.FullMulProduct
import Mathlib.Data.Nat.Factorization.Basic

/-! The power-of-two factor selected by the full-precision division routine. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

theorem odd_and_power_sub {n m : Nat} (hm : Odd m) (hbound : m < 2 ^ n) :
    m &&& (2 ^ n - m) = 1 := by
  obtain ⟨q, rfl⟩ := hm
  cases n with
  | zero => simp only [pow_zero] at hbound; omega
  | succ n =>
      have hq : q < 2 ^ n := by rw [pow_succ] at hbound; omega
      have hneg : 2 ^ (n + 1) - (2 * q + 1) = 2 * (2 ^ n - (q + 1)) + 1 := by
        rw [pow_succ]
        omega
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_and, hneg]
      cases i with
      | zero => simp
      | succ i =>
          simp only [Nat.testBit_succ, show (2 * q + 1) / 2 = q by omega,
            show (2 * (2 ^ n - (q + 1)) + 1) / 2 = 2 ^ n - (q + 1) by omega]
          rw [Nat.testBit_two_pow_sub_succ hq]
          simp only [show 1 / 2 = 0 by rfl, Nat.zero_testBit, Bool.and_left_comm,
            Bool.and_not_self, Bool.and_false]

theorem power_factor_and_sub {n k m : Nat} (hk : k < n) (hm : Odd m)
    (hbound : 2 ^ k * m < 2 ^ n) :
    (2 ^ k * m) &&& (2 ^ n - 2 ^ k * m) = 2 ^ k := by
  have hpow : 2 ^ n = 2 ^ k * 2 ^ (n - k) := by rw [← pow_add, Nat.add_sub_of_le (by omega)]
  have hsmall : m < 2 ^ (n - k) := by
    rw [hpow] at hbound
    exact Nat.lt_of_mul_lt_mul_left hbound
  rw [hpow, ← Nat.mul_sub_left_distrib]
  rw [Nat.mul_comm (2 ^ k) m, Nat.mul_comm (2 ^ k) (2 ^ (n - k) - m)]
  rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_and_distrib,
    odd_and_power_sub hm hsmall, Nat.shiftLeft_eq, Nat.one_mul]

def fullDivTwos (d : UInt256) : UInt256 := UInt256.land d (UInt256.sub ⟨0⟩ d)

theorem fullDivTwos_decomposition (d : UInt256) (hd : d ≠ ⟨0⟩) :
    ∃ k m : Nat, k < 256 ∧ Odd m ∧ d.toNat = 2 ^ k * m ∧ (fullDivTwos d).toNat = 2 ^ k := by
  have hpos : 0 < d.toNat := Nat.pos_of_ne_zero (fun h ↦ hd (uint256_toNat_eq_zero h))
  obtain ⟨k, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt hpos)
  have hmpos : 0 < m := by rw [he] at hpos; exact Nat.pos_of_mul_pos_left hpos
  have hbound : 2 ^ k * m < 2 ^ 256 := by rw [← he]; exact d.val.isLt
  have hk : k < 256 := by
    have hpow : 2 ^ k < 2 ^ 256 := lt_of_le_of_lt
      (Nat.le_mul_of_pos_right _ hmpos) hbound
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hpow
  refine ⟨k, m, hk, hm, he, ?_⟩
  rw [fullDivTwos, u256_land_toNat, usub_toNat_underflow (by simpa using hpos)]
  change (d.toNat &&& (2 ^ 256 + 0 - d.toNat)) % (2 ^ 256) = 2 ^ k
  rw [Nat.add_zero, he, power_factor_and_sub hk hm hbound, Nat.mod_eq_of_lt]
  exact Nat.pow_lt_pow_right (by decide) hk

end Benchmarks.Morpho.MetaMorphoV1_1

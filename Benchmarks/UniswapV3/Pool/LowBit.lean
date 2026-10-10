import Benchmarks.UniswapV3.Pool.ModularWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: a natural number and its bounded bitwise complement are disjoint.
theorem nat_and_complement {n w : Nat} (h : n < 2 ^ w) :
    (2 ^ w - (n + 1)) &&& n = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_succ h]
  simp [Bool.and_assoc]

-- LIBRARY CANDIDATE: isolating the least set bit factors out exactly the power of two.
theorem nat_lowBit_factor (w n : Nat) (hn : 0 < n) (hw : n < 2 ^ w) :
    ∃ k m, k < w ∧ m % 2 = 1 ∧ n = 2 ^ k * m ∧
      (2 ^ w - n) &&& n = 2 ^ k := by
  induction w generalizing n with
  | zero => simp only [pow_zero] at hw; omega
  | succ w ih =>
    have hhalf : n / 2 < 2 ^ w := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa only [pow_succ] using hw
    have heq := Nat.mod_add_div n 2
    by_cases heven : n % 2 = 0
    · have hp : 0 < n / 2 := by omega
      obtain ⟨k, m, hk, hm, hfac, hand⟩ := ih (n / 2) hp hhalf
      refine ⟨k + 1, m, by omega, hm, ?_, ?_⟩
      · rw [pow_succ]
        nlinarith
      · have hdiv : (2 ^ (w + 1) - n) / 2 = 2 ^ w - n / 2 := by
          rw [pow_succ]
          omega
        have hmod : ((2 ^ (w + 1) - n) &&& n) % 2 = 0 := by
          have h := Nat.and_mod_two_pow (a := 2 ^ (w + 1) - n) (b := n) (n := 1)
          simpa only [pow_one, heven, Nat.and_zero] using h
        have hdivand : ((2 ^ (w + 1) - n) &&& n) / 2 = 2 ^ k := by
          rw [Nat.and_div_two, hdiv, hand]
        have h := Nat.mod_add_div ((2 ^ (w + 1) - n) &&& n) 2
        calc
          _ = 2 * 2 ^ k := by omega
          _ = 2 ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]
    · have hodd : n % 2 = 1 := by omega
      refine ⟨0, n, by omega, hodd, by simp, ?_⟩
      have hdiv : (2 ^ (w + 1) - n) / 2 = 2 ^ w - (n / 2 + 1) := by
        rw [pow_succ]
        omega
      have hdivand : ((2 ^ (w + 1) - n) &&& n) / 2 = 0 := by
        rw [Nat.and_div_two, hdiv, nat_and_complement hhalf]
      have hmod : ((2 ^ (w + 1) - n) &&& n) % 2 = 1 := by
        rw [Nat.and_mod_two_eq_one]
        constructor
        · rw [pow_succ]
          omega
        · exact hodd
      have h := Nat.mod_add_div ((2 ^ (w + 1) - n) &&& n) 2
      omega

def wordLowBit (n : UInt256) : UInt256 := UInt256.land (UInt256.sub ⟨0⟩ n) n

theorem wordLowBit_factor (n : UInt256) (hn : 0 < n.toNat) :
    ∃ k m, k < 256 ∧ m % 2 = 1 ∧ n.toNat = 2 ^ k * m ∧
      (wordLowBit n).toNat = 2 ^ k := by
  obtain ⟨k, m, hk, hm, hfac, hand⟩ := nat_lowBit_factor 256 n.toNat hn n.val.isLt
  refine ⟨k, m, hk, hm, hfac, ?_⟩
  rw [wordLowBit, uland_toNat, usub_toNat_underflow (by exact hn)]
  simpa only [Nat.add_zero] using hand

end Benchmarks.UniswapV3.Pool

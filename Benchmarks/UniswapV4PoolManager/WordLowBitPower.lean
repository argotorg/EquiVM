import Benchmarks.UniswapV4PoolManager.WordLowBit

open Ethereum Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: a bounded natural and its finite complement are disjoint.
theorem natMaskComplementAnd {n k : Nat} (hn : n < 2^k) :
    (2^k-(n+1)) &&& n = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_succ hn]
  simp only [Nat.zero_testBit, Bool.and_assoc, Bool.not_and_self, Bool.and_false]

-- LIBRARY CANDIDATE: isolating the lowest bit of a positive bounded natural yields a power of two.
theorem natLowBit_power {n k : Nat} (hpos : 0 < n) (hlt : n < 2^k) :
    ∃ j, j < k ∧ (2^k-n) &&& n = 2^j := by
  induction k generalizing n with
  | zero => simp only [Nat.pow_zero] at hlt; omega
  | succ k ih =>
    rw [Nat.pow_succ] at hlt ⊢
    by_cases he : n%2 = 0
    · obtain ⟨j, hj, hp⟩ := ih (n := n/2) (by omega) (by omega)
      have hd : (2^k*2-n)/2 = 2^k-n/2 := by omega
      have hdiv : ((2^k*2-n) &&& n)/2 = 2^j := by
        rw [Nat.and_div_two, hd, hp]
      have hmod : ((2^k*2-n) &&& n)%2 = 0 := by
        change ((2^k*2-n) &&& n)%2^1 = 0
        rw [Nat.and_mod_two_pow]
        change ((2^k*2-n)%2 &&& n%2) = 0
        rw [he, Nat.and_zero]
      refine ⟨j+1, by omega, ?_⟩
      rw [Nat.pow_succ]
      omega
    · have hn : n%2 = 1 := by omega
      have hd : (2^k*2-n)/2 = 2^k-(n/2+1) := by omega
      have hdiv : ((2^k*2-n) &&& n)/2 = 0 := by
        rw [Nat.and_div_two, hd, natMaskComplementAnd (by omega : n/2 < 2^k)]
      have hmod : ((2^k*2-n) &&& n)%2 = 1 := by
        change ((2^k*2-n) &&& n)%2^1 = 1
        rw [Nat.and_mod_two_pow]
        change ((2^k*2-n)%2 &&& n%2) = 1
        rw [show (2^k*2-n)%2 = 1 by omega, hn]
        rfl
      exact ⟨0, by omega, by change _ = 1; omega⟩

-- LIBRARY CANDIDATE: the lowest-bit mask of a nonzero EVM word is one of its 256 bit values.
theorem wordLowBit_power (w : UInt256) (hw : w ≠ ⟨0⟩) :
    ∃ j : Fin 256, UInt256.land (UInt256.sub ⟨0⟩ w) w = UInt256.ofNat (2^j.val) := by
  have hpos : 0 < w.toNat := by
    by_contra h
    exact hw (uint256_toNat_eq_zero (by omega))
  obtain ⟨j, hj, he⟩ := natLowBit_power (k := 256) hpos w.val.isLt
  refine ⟨⟨j, hj⟩, u256_inj ?_⟩
  rw [uland_toNat, usub_toNat_underflow (a := ⟨0⟩) (b := w) hpos]
  change (2^256-w.toNat) &&& w.toNat = (UInt256.ofNat (2^j)).toNat
  rw [he, UInt256.toNat_ofNat_of_lt (show 2^j < UInt256.size from
    Nat.pow_lt_pow_right (by decide) hj)]

end Benchmarks.UniswapV4PoolManager

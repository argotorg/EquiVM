import Benchmarks.UniswapV4PoolManager.SignedRemainderWords

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: rounding a quotient up cannot exceed its numerator.
theorem divRound_le (n d : Nat) (hd : 0 < d) :
    n/d + (if 0 < n%d then 1 else 0) ≤ n := by
  have hdiv := Nat.div_le_self n d
  have hmul : n/d ≤ d*(n/d) := by
    calc
      n/d = 1*(n/d) := (Nat.one_mul _).symm
      _ ≤ d*(n/d) := Nat.mul_le_mul_right _ hd
  have hdecomp := Nat.mod_add_div n d
  split <;> omega

def divRoundWord (x y : UInt256) : UInt256 :=
  UInt256.div x y + UInt256.isZero (UInt256.isZero (UInt256.mod x y))

theorem divRoundWord_zero (x : UInt256) : divRoundWord x ⟨0⟩ = ⟨0⟩ := by
  apply u256_inj
  simp only [divRoundWord, uadd_toNat, udiv_toNat]
  change (x.toNat / 0 + 0) % UInt256.size = 0
  simp

theorem divRoundWord_toNat {x y : UInt256} (hy : y ≠ ⟨0⟩) :
    (divRoundWord x y).toNat = x.toNat/y.toNat + (if 0 < x.toNat%y.toNat then 1 else 0) := by
  have hyn : y.toNat ≠ 0 := fun he => hy (uint256_toNat_eq_zero he)
  have hmod := wordMod_toNat (a := x) hyn
  have hb := lt_of_le_of_lt (divRound_le x.toNat y.toNat (Nat.pos_of_ne_zero hyn)) x.val.isLt
  rw [divRoundWord, uadd_toNat, udiv_toNat]
  by_cases hz : UInt256.mod x y = ⟨0⟩
  · have hn : x.toNat%y.toNat = 0 := by rw [← hmod, hz]; rfl
    simp only [hn, Nat.lt_irrefl, if_false] at hb ⊢
    rw [hz]
    change (x.toNat/y.toNat + 0) % UInt256.size = x.toNat/y.toNat + 0
    exact Nat.mod_eq_of_lt hb
  · have hn : 0 < x.toNat%y.toNat := by
      by_contra he
      apply hz
      apply u256_inj
      rw [hmod]
      change x.toNat%y.toNat = 0
      omega
    rw [isZero_eq_zero_of_ne hz]
    simp only [if_pos hn] at hb ⊢
    change (x.toNat/y.toNat + 1) % UInt256.size = x.toNat/y.toNat + 1
    exact Nat.mod_eq_of_lt hb

end Benchmarks.UniswapV4PoolManager

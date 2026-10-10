import Benchmarks.UniswapV3.Pool.LowBit

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: subtracting a single word from a two-word unsigned integer.
theorem wordPair_sub (hi lo r : UInt256)
    (hr : r.toNat ≤ lo.toNat + UInt256.size * hi.toNat) :
    (UInt256.sub lo r).toNat + UInt256.size *
      (UInt256.sub hi (UInt256.gt r lo)).toNat =
      lo.toNat + UInt256.size * hi.toNat - r.toNat := by
  by_cases h : r.toNat ≤ lo.toNat
  · rw [ugt_zero h, usub_toNat h, usub_toNat (a := hi) (b := ⟨0⟩) (Nat.zero_le _)]
    change lo.toNat - r.toNat + UInt256.size * (hi.toNat - 0) = _
    simp only [Nat.sub_zero]
    omega
  · have hlt : lo.toNat < r.toNat := by omega
    have hp : 0 < hi.toNat := by
      by_contra hn
      have hz : hi.toNat = 0 := by omega
      rw [hz, Nat.mul_zero, Nat.add_zero] at hr
      omega
    rw [ugt_one hlt, usub_toNat_underflow hlt,
      usub_toNat (a := hi) (b := ⟨1⟩) hp]
    change UInt256.size + lo.toNat - r.toNat + UInt256.size * (hi.toNat - 1) = _
    have hh : hi.toNat - 1 + 1 = hi.toNat := by omega
    have hrl : r.toNat < UInt256.size := r.val.isLt
    have hlo : r.toNat ≤ UInt256.size + lo.toNat := by omega
    have hrhs := Nat.sub_add_cancel hr
    have hlhs := Nat.sub_add_cancel hlo
    nlinarith

-- LIBRARY CANDIDATE: the reciprocal scaling used to shift a two-word value right.
theorem word_pow_two_flip (k : Nat) (hk : k < 256) :
    (⟨1⟩ : UInt256) + UInt256.div (UInt256.sub ⟨0⟩ (UInt256.ofNat (2 ^ k)))
      (UInt256.ofNat (2 ^ k)) = UInt256.ofNat (2 ^ (256 - k)) := by
  have hp : 0 < 2 ^ k := Nat.two_pow_pos k
  have ht := UInt256.toNat_ofNat_of_lt (pow_lt_size hk)
  have hn : UInt256.size = 2 ^ k * 2 ^ (256 - k) := by
    rw [← pow_add, Nat.add_sub_of_le (by omega)]
    rfl
  have hq : 0 < 2 ^ (256 - k) := Nat.two_pow_pos _
  have hdiv : (UInt256.size - 2 ^ k) / 2 ^ k = 2 ^ (256 - k) - 1 := by
    simpa only [Nat.mul_one, hn, Nat.mul_div_right _ hp] using
      Nat.sub_mul_div UInt256.size (2 ^ k) 1
  apply u256_inj
  rw [uadd_toNat, udiv_toNat, usub_toNat_underflow (by simpa only [ht] using hp), ht]
  change (1 + (UInt256.size + 0 - 2 ^ k) / 2 ^ k) % UInt256.size = _
  rw [Nat.add_zero, hdiv, show 1 + (2 ^ (256 - k) - 1) = 2 ^ (256 - k) by omega]
  rfl

-- LIBRARY CANDIDATE: quotient limbs can be joined with bitwise OR after a power-of-two shift.
theorem wordPair_div_pow_two (hi lo : UInt256) (k : Nat) (hk : k < 256) :
    UInt256.lor (UInt256.div lo (UInt256.ofNat (2 ^ k)))
      (UInt256.mul hi (UInt256.ofNat (2 ^ (256 - k)))) =
      UInt256.ofNat ((lo.toNat + UInt256.size * hi.toNat) / 2 ^ k) := by
  have hp : 0 < 2 ^ k := Nat.two_pow_pos k
  have ht := UInt256.toNat_ofNat_of_lt (pow_lt_size hk)
  have hN : UInt256.size = 2 ^ (256 - k) * 2 ^ k := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rfl
  have hlo : lo.toNat / 2 ^ k < 2 ^ (256 - k) := by
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    rw [← hN]
    exact lo.val.isLt
  have hmul : (UInt256.mul hi (UInt256.ofNat (2 ^ (256 - k)))).toNat =
      (hi.toNat % 2 ^ k) * 2 ^ (256 - k) := by
    rw [u256_mul_toNat]
    change (hi.toNat * (2 ^ (256 - k) % UInt256.size)) % UInt256.size = _
    rw [Nat.mul_mod_mod, hN, Nat.mul_comm (2 ^ (256 - k)), Nat.mul_mod_mul_right]
  apply u256_inj
  rw [u256_lor_toNat, udiv_toNat, ht, hmul, nat_lor_shift_add _ _ _ hlo]
  change (lo.toNat / 2 ^ k + hi.toNat % 2 ^ k * 2 ^ (256 - k)) % UInt256.size =
    ((lo.toNat + UInt256.size * hi.toNat) / 2 ^ k) % UInt256.size
  have hdiv : (lo.toNat + UInt256.size * hi.toNat) / 2 ^ k =
      lo.toNat / 2 ^ k + hi.toNat * 2 ^ (256 - k) := by
    rw [hN]
    have heq : 2 ^ (256 - k) * 2 ^ k * hi.toNat =
        hi.toNat * 2 ^ (256 - k) * 2 ^ k := by ring
    rw [heq, Nat.add_mul_div_right _ _ hp]
  rw [hdiv]
  have hmod : (hi.toNat * 2 ^ (256 - k)) % UInt256.size =
      (hi.toNat % 2 ^ k) * 2 ^ (256 - k) := by
    rw [hN, Nat.mul_comm (2 ^ (256 - k)), Nat.mul_mod_mul_right]
  rw [Nat.add_mod, ← hmod, Nat.mod_mod, ← Nat.add_mod]

end Benchmarks.UniswapV3.Pool

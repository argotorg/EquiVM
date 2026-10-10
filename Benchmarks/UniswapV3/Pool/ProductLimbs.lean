import Benchmarks.UniswapV3.Pool.FullMathSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: Chinese remainder reconstruction of the high product limb.
theorem nat_crt_limbs {p M : Nat} (hM : 1 < M) (hp : p < (M - 1) * M) :
    (p % M ≤ p % (M - 1) ∧ p % (M - 1) = p % M + p / M) ∨
    (p % (M - 1) < p % M ∧ p % (M - 1) + M = p % M + p / M + 1) := by
  have hh : p / M < M - 1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hp
  have hl : p % M < M := Nat.mod_lt _ (by omega)
  have hmod : p % (M - 1) = (p % M + p / M) % (M - 1) := by
    have heq : p = (M - 1) * (p / M) + (p % M + p / M) := by
      have := Nat.mod_add_div p M
      have : M = M - 1 + 1 := by omega
      nlinarith [Nat.mul_add (M - 1) (p / M) 1]
    conv_lhs => rw [heq]
    rw [Nat.mul_add_mod_self_left]
  by_cases h : p % M + p / M < M - 1
  · rw [Nat.mod_eq_of_lt h] at hmod
    exact Or.inl ⟨by rw [hmod]; exact Nat.le_add_right _ _, hmod⟩
  · have hs : (p % M + p / M) % (M - 1) = p % M + p / M - (M - 1) := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hs] at hmod
    exact Or.inr ⟨by omega, by omega⟩

theorem mulMod_toNat (a b d : UInt256) (hd : 0 < d.toNat) :
    (UInt256.mulMod a b d).toNat = a.toNat * b.toNat % d.toNat := by
  have hzero : UInt256.eq0 d = false := by
    simp only [UInt256.eq0]
    exact decide_eq_false (fun h ↦ (Nat.ne_of_gt hd) (congrArg Fin.val h))
  rw [UInt256.mulMod, hzero]
  exact UInt256.toNat_ofNat_of_lt (lt_trans (Nat.mod_lt _ hd) d.val.isLt)

def productHigh (a b : UInt256) : UInt256 :=
  let r := UInt256.mulMod a b (UInt256.lnot ⟨0⟩)
  let lo := UInt256.mul a b
  UInt256.sub (UInt256.sub r lo) (UInt256.lt r lo)

theorem productHigh_toNat (a b : UInt256) :
    (productHigh a b).toNat = fullMathProduct a b / UInt256.size := by
  have hmax : (UInt256.lnot ⟨0⟩).toNat = UInt256.size - 1 := by decide +kernel
  have hm : 1 < UInt256.size := by decide
  have ha := a.val.isLt
  have hb := b.val.isLt
  have hp : fullMathProduct a b < (UInt256.size - 1) * UInt256.size := by
    unfold fullMathProduct
    have ha' : a.toNat ≤ UInt256.size - 1 := by exact Nat.le_sub_one_of_lt ha
    have hb' : b.toNat ≤ UInt256.size - 1 := by exact Nat.le_sub_one_of_lt hb
    have := Nat.mul_le_mul ha' hb'
    have hsize : UInt256.size - 1 + 1 = UInt256.size := by omega
    nlinarith
  have hr := mulMod_toNat a b (UInt256.lnot ⟨0⟩) (by rw [hmax]; omega)
  rw [hmax] at hr
  have hl := u256_mul_toNat a b
  change (UInt256.mul a b).toNat = fullMathProduct a b % UInt256.size at hl
  change (UInt256.mulMod a b (UInt256.lnot ⟨0⟩)).toNat =
    fullMathProduct a b % (UInt256.size - 1) at hr
  rcases nat_crt_limbs hm hp with ⟨hle, heq⟩ | ⟨hlt, heq⟩
  · have hc : UInt256.lt (UInt256.mulMod a b (UInt256.lnot ⟨0⟩)) (UInt256.mul a b) = ⟨0⟩ := by
      apply ult_zero
      rw [hr, hl]
      exact hle
    rw [productHigh, hc, usub_toNat (by simp), usub_toNat (by rw [hr, hl]; exact hle), hr, hl]
    change fullMathProduct a b % (UInt256.size - 1) -
      fullMathProduct a b % UInt256.size - 0 = _
    omega
  · have hc : UInt256.lt (UInt256.mulMod a b (UInt256.lnot ⟨0⟩)) (UInt256.mul a b) = ⟨1⟩ := by
      apply ult_one
      rw [hr, hl]
      exact hlt
    have hsub := usub_toNat_underflow
      (a := UInt256.mulMod a b (UInt256.lnot ⟨0⟩)) (b := UInt256.mul a b)
      (by rw [hr, hl]; exact hlt)
    rw [hr, hl] at hsub
    rw [Nat.add_comm UInt256.size, heq, Nat.add_assoc, Nat.add_sub_cancel_left] at hsub
    rw [productHigh, hc, usub_toNat (by rw [hsub]; exact Nat.le_add_left 1 _), hsub]
    exact Nat.add_sub_cancel _ 1

end Benchmarks.UniswapV3.Pool

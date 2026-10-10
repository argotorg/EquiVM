import Benchmarks.Morpho.MetaMorphoV1_1.Arithmetic

/-! Reconstruction of the high word of a full 512-bit product from MUL and MULMOD. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def fullProductHigh (a b : UInt256) : UInt256 :=
  UInt256.sub
    (UInt256.sub (UInt256.mulMod a b (UInt256.lnot ⟨0⟩)) (UInt256.mul a b))
    (UInt256.lt (UInt256.mulMod a b (UInt256.lnot ⟨0⟩)) (UInt256.mul a b))

theorem wordMulMod_toNat (a b d : UInt256) (hd : d ≠ ⟨0⟩) :
    (UInt256.mulMod a b d).toNat = (a.toNat * b.toNat) % d.toNat := by
  have hz : UInt256.eq0 d = false := by
    simpa only [UInt256.eq0, beq_eq_false_iff_ne] using hd
  have hpos : 0 < d.toNat := Nat.pos_of_ne_zero (fun h ↦ hd (uint256_toNat_eq_zero h))
  rw [UInt256.mulMod, hz]
  exact UInt256.toNat_ofNat_of_lt (lt_trans (Nat.mod_lt _ hpos) d.val.isLt)

theorem productHigh_lt_max (a b : UInt256) :
    a.toNat * b.toNat / UInt256.size < UInt256.size - 1 := by
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < UInt256.size)).mpr
  have ha' : a.toNat < UInt256.size := a.val.isLt
  have hb' : b.toNat < UInt256.size := b.val.isLt
  have ha : a.toNat ≤ UInt256.size - 1 := by omega
  have hb : b.toNat ≤ UInt256.size - 1 := by omega
  exact lt_of_le_of_lt (Nat.mul_le_mul ha hb)
    (Nat.mul_lt_mul_of_pos_left (by decide) (by decide))

theorem product_mod_max (a b : UInt256) :
    a.toNat * b.toNat % (UInt256.size - 1) =
      (a.toNat * b.toNat / UInt256.size + a.toNat * b.toNat % UInt256.size) %
        (UInt256.size - 1) := by
  conv_lhs => rw [← Nat.mod_add_div (a.toNat * b.toNat) UInt256.size]
  have hm : (UInt256.size * (a.toNat * b.toNat / UInt256.size)) % (UInt256.size - 1) =
      (a.toNat * b.toNat / UInt256.size) % (UInt256.size - 1) := by
    rw [Nat.mul_mod, show UInt256.size % (UInt256.size - 1) = 1 from by decide,
      Nat.one_mul, Nat.mod_mod]
  rw [Nat.add_mod, hm, ← Nat.add_mod, Nat.add_comm]

theorem fullProductHigh_toNat (a b : UInt256) :
    (fullProductHigh a b).toNat = a.toNat * b.toNat / UInt256.size := by
  let hi := a.toNat * b.toNat / UInt256.size
  let lo := a.toNat * b.toNat % UInt256.size
  have hhi : hi < UInt256.size - 1 := productHigh_lt_max a b
  have hlo : lo < UInt256.size := Nat.mod_lt _ (by decide)
  have hm : (UInt256.mulMod a b (UInt256.lnot ⟨0⟩)).toNat =
      (hi + lo) % (UInt256.size - 1) := by
    rw [wordMulMod_toNat _ _ _ (by decide), u256_lnot_zero_toNat, product_mod_max]
  have hp : (UInt256.mul a b).toNat = lo := u256_mul_toNat a b
  unfold fullProductHigh
  by_cases hsum : hi + lo < UInt256.size - 1
  · have hm' : (UInt256.mulMod a b (UInt256.lnot ⟨0⟩)).toNat = hi + lo := by
      rw [hm, Nat.mod_eq_of_lt hsum]
    have hle : (UInt256.mul a b).toNat ≤
        (UInt256.mulMod a b (UInt256.lnot ⟨0⟩)).toNat := by
      rw [hm', hp]
      exact Nat.le_add_left _ _
    rw [ult_zero hle, usub_toNat (by simp), usub_toNat hle, hm', hp]
    simp only [UInt256.zero_toNat, Nat.sub_zero, Nat.add_sub_cancel_right]
    rfl
  · have hm' : (UInt256.mulMod a b (UInt256.lnot ⟨0⟩)).toNat =
        hi + lo - (UInt256.size - 1) := by
      rw [hm, Nat.mod_eq_sub_mod (Nat.le_of_not_gt hsum), Nat.mod_eq_of_lt (by omega)]
    have hlt : (UInt256.mulMod a b (UInt256.lnot ⟨0⟩)).toNat <
        (UInt256.mul a b).toNat := by rw [hm', hp]; omega
    have hsub : (UInt256.sub (UInt256.mulMod a b (UInt256.lnot ⟨0⟩))
        (UInt256.mul a b)).toNat = hi + 1 := by
      rw [usub_toNat_underflow hlt, hm', hp]
      omega
    rw [ult_one hlt, usub_toNat (by rw [hsub]; change 1 ≤ hi + 1; omega), hsub]
    change hi + 1 - 1 = hi
    omega

theorem fullProductHigh_eq_zero_iff (a b : UInt256) :
    fullProductHigh a b = ⟨0⟩ ↔ a.toNat * b.toNat < UInt256.size := by
  constructor
  · intro hz
    have h := fullProductHigh_toNat a b
    rw [hz] at h
    change 0 = a.toNat * b.toNat / UInt256.size at h
    have hsize : 0 < UInt256.size := by decide
    have hdiv := (Nat.div_lt_iff_lt_mul hsize).mp
      (show a.toNat * b.toNat / UInt256.size < 1 by omega)
    simpa only [Nat.one_mul] using hdiv
  · intro h
    apply uint256_toNat_eq_zero
    rw [fullProductHigh_toNat, Nat.div_eq_of_lt h]

def fullProductGuard (a b : UInt256) : UInt256 :=
  UInt256.eq (UInt256.sub (UInt256.mulMod a b (UInt256.lnot ⟨0⟩)) (UInt256.mul a b))
    (UInt256.lt (UInt256.mulMod a b (UInt256.lnot ⟨0⟩)) (UInt256.mul a b))

theorem fullProductGuard_small {a b : UInt256} (h : a.toNat * b.toNat < UInt256.size) :
    fullProductGuard a b = ⟨1⟩ := by
  have he := u256_sub_eq_zero_iff_eq.mp ((fullProductHigh_eq_zero_iff a b).mpr h)
  unfold fullProductGuard
  rw [he, uInt256_eq_self]

theorem fullProductGuard_large {a b : UInt256} (h : UInt256.size ≤ a.toNat * b.toNat) :
    fullProductGuard a b = ⟨0⟩ := by
  have hne : UInt256.sub (UInt256.mulMod a b (UInt256.lnot ⟨0⟩)) (UInt256.mul a b) ≠
      UInt256.lt (UInt256.mulMod a b (UInt256.lnot ⟨0⟩)) (UInt256.mul a b) := by
    intro he
    have hz : fullProductHigh a b = ⟨0⟩ := u256_sub_eq_zero_iff_eq.mpr he
    exact Nat.not_lt_of_ge h ((fullProductHigh_eq_zero_iff a b).mp hz)
  exact u256_eq_of_ne hne

def fullMulDivFits (a b d : UInt256) : Prop :=
  d ≠ ⟨0⟩ ∧ a.toNat * b.toNat / d.toNat < UInt256.size

def fullMulDivWord (a b d : UInt256) : UInt256 := UInt256.ofNat (a.toNat * b.toNat / d.toNat)

theorem fullMulDivFits_iff (a b d : UInt256) :
    fullMulDivFits a b d ↔ (fullProductHigh a b).toNat < d.toNat := by
  rw [fullProductHigh_toNat]
  constructor
  · rintro ⟨hd, hfit⟩
    have hpos : 0 < d.toNat := Nat.pos_of_ne_zero (fun h ↦ hd (uint256_toNat_eq_zero h))
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < UInt256.size)).mpr
    simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hpos).mp hfit
  · intro h
    have hpos : 0 < d.toNat := Nat.zero_lt_of_lt h
    refine ⟨?_, (Nat.div_lt_iff_lt_mul hpos).mpr ?_⟩
    · intro hz
      rw [hz] at hpos
      exact Nat.not_lt_zero _ hpos
    · simpa only [Nat.mul_comm] using
        (Nat.div_lt_iff_lt_mul (by decide : 0 < UInt256.size)).mp h

end Benchmarks.Morpho.MetaMorphoV1_1

import Benchmarks.UniswapV3.Pool.Common
import Mathlib.Data.Nat.Bitwise

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: Reasoning.EVMWord, set all high bits of a bounded natural.
theorem natLorHighMask (n k total : Nat) (hn : n < 2 ^ total) (hk : k ≤ total) :
    n ||| (2 ^ total - 2 ^ k) = n % 2 ^ k + (2 ^ total - 2 ^ k) := by
  have hm : 2 ^ total - 2 ^ k = (2 ^ (total - k) - 1) <<< k := by
    rw [Nat.shiftLeft_eq, Nat.sub_mul, one_mul, ← Nat.pow_add,
      Nat.sub_add_cancel hk]
  rw [hm, Nat.shiftLeft_eq, ← nat_lor_shift_add _ _ _ (Nat.mod_lt _ (by positivity))]
  simp only [← Nat.shiftLeft_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  change (n ||| (2 ^ (total - k) - 1) <<< k).testBit i =
    (n % 2 ^ k ||| (2 ^ (total - k) - 1) <<< k).testBit i
  simp only [Nat.testBit_or, testBit_shiftLeft, Nat.testBit_mod_two_pow,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : i < k
  · simp [hi]
  · by_cases hit : i < total
    · have hdiff : i - k < total - k := by omega
      simp [hi, hdiff]
    · have hdiff : ¬ i - k < total - k := by omega
      have hbit : n.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hn
          (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hi, hdiff, hbit]

-- LIBRARY CANDIDATE: Reasoning.EVMWord, characterize a sign bit through the low-bit residue.
theorem testBit_eq_true_iff_half_le (n k : Nat) :
    n.testBit k = true ↔ 2 ^ k ≤ n % 2 ^ (k + 1) := by
  have hm := Nat.mod_lt n (show 0 < 2 ^ (k + 1) by positivity)
  have hbit : (n % 2 ^ (k + 1)).testBit k = n.testBit k := by
    simp only [Nat.testBit_mod_two_pow, Nat.lt_succ_self, decide_true, Bool.true_and]
  rw [← hbit]
  by_cases hhalf : 2 ^ k ≤ n % 2 ^ (k + 1)
  · simp only [Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hhalf hm, hhalf]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_not_ge hhalf)]
    simp only [Bool.false_eq_true, hhalf]

-- LIBRARY CANDIDATE: Reasoning.WordArithmetic, signed normalization stays in the declared range.
theorem normalizeSint_bounds (width : ABI.BitWidth) (i : Int) :
    -Int.ofNat (EVM.twoPow (width.val - 1)) ≤ normalizeInt (.sint width) i ∧
      normalizeInt (.sint width) i < Int.ofNat (EVM.twoPow (width.val - 1)) := by
  have hpos : 0 < Int.ofNat (EVM.twoPow width.val) := by
    exact Int.ofNat_lt.mpr (Nat.two_pow_pos width.val)
  have hm : Int.ofNat (EVM.twoPow width.val) =
      2 * Int.ofNat (EVM.twoPow (width.val - 1)) := by
    have hw : width.val = (width.val - 1) + 1 := by have := width.property; omega
    conv_lhs => rw [hw]
    simp only [EVM.twoPow, pow_succ, Int.ofNat_eq_natCast, Int.natCast_mul]
    omega
  have hr0 := Int.emod_nonneg i (ne_of_gt hpos)
  have hrlt := Int.emod_lt_of_pos i hpos
  simp only [normalizeInt]
  split <;> omega

-- LIBRARY CANDIDATE: Reasoning.ABI, encode a signed scalar in its declared range.
theorem sintReturnEncoding (width : ABI.BitWidth) (i : Int)
    (hlo : -Int.ofNat (EVM.twoPow (width.val - 1)) ≤ i)
    (hhi : i < Int.ofNat (EVM.twoPow (width.val - 1))) :
    encodeReturnValue? (.elem (.int (.sint width))) (.int i) =
      some (UInt256.toByteArray (EVM.wordOfInt i)) := by
  refine scalarReturnEncoding rfl ?_ ?_
  · simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
    cases width; rfl
  · simp only [encodeABIValue?, encodeABIWord?,
      if_neg (Nat.ne_of_gt width.property.1), if_pos (And.intro hlo hhi),
      bind, Option.bind]

-- LIBRARY CANDIDATE: Reasoning.WordArithmetic, encode normalized signed residues as words.
theorem wordOfInt_normalizeSint_toNat (width : ABI.BitWidth) (w : UInt256) :
    (EVM.wordOfInt (normalizeInt (.sint width) (Int.ofNat w.toNat))).toNat =
      if w.toNat % 2 ^ width.val < 2 ^ (width.val - 1) then w.toNat % 2 ^ width.val
      else UInt256.size - (2 ^ width.val - w.toNat % 2 ^ width.val) := by
  have hmod : w.toNat % 2 ^ width.val < 2 ^ width.val := Nat.mod_lt _ (by positivity)
  have hwidth : 2 ^ width.val ≤ UInt256.size :=
    Nat.pow_le_pow_right (by decide) width.property.2.1
  have hres : Int.ofNat w.toNat % Int.ofNat (EVM.twoPow width.val) =
      Int.ofNat (w.toNat % 2 ^ width.val) := rfl
  rw [normalizeInt, hres]
  simp only [EVM.twoPow, Int.ofNat_eq_natCast]
  by_cases h : w.toNat % 2 ^ width.val < 2 ^ (width.val - 1)
  · rw [if_pos (Int.ofNat_lt.mpr h), if_pos h]
    change (EVM.wordOfInt (Int.ofNat (w.toNat % 2 ^ width.val))).toNat = _
    rw [wordOfInt_ofNat_toNat_gen]
    exact ulit_toNat' _ (lt_of_lt_of_le hmod hwidth)
  · rw [if_neg (by exact_mod_cast h), if_neg h]
    have hneg : (↑(w.toNat % 2 ^ width.val) : Int) - (2 ^ width.val : Nat) < 0 := by
      omega
    have habs : ((↑(w.toNat % 2 ^ width.val) : Int) - (2 ^ width.val : Nat)).natAbs =
        2 ^ width.val - w.toNat % 2 ^ width.val := by
      omega
    rw [wordOfInt_toNat_of_neg_of_abs_lt _ hneg (by
      rw [habs]
      have hp : 0 < 2 ^ (width.val - 1) := by positivity
      change 2 ^ width.val - w.toNat % 2 ^ width.val < UInt256.size
      omega), habs]

-- LIBRARY CANDIDATE: Reasoning.WordArithmetic, SIGNEXTEND implements a signed narrowing cast.
theorem signextend_normalizeSint (width : ABI.BitWidth) (a w : UInt256)
    (ha : a.toNat ≤ 31)
    (hsign : (UInt256.shiftLeft ⟨1⟩ (UInt256.add (UInt256.mul a ⟨8⟩) ⟨7⟩)).toNat =
      2 ^ (width.val - 1)) :
    UInt256.signextend a w =
      EVM.wordOfInt (normalizeInt (.sint width) (Int.ofNat w.toNat)) := by
  let s := UInt256.shiftLeft ⟨1⟩ (UInt256.add (UInt256.mul a ⟨8⟩) ⟨7⟩)
  have hs : s.toNat = 2 ^ (width.val - 1) := hsign
  have hpos : 0 < 2 ^ (width.val - 1) := by positivity
  have hw : width.val = (width.val - 1) + 1 := by have := width.property; omega
  have hdouble : 2 ^ width.val = 2 * 2 ^ (width.val - 1) := by
    conv_lhs => rw [hw]
    rw [pow_succ, Nat.mul_comm]
  have hmod : w.toNat % 2 ^ width.val < 2 ^ width.val := Nat.mod_lt _ (by positivity)
  have hwidth : 2 ^ width.val ≤ UInt256.size :=
    Nat.pow_le_pow_right (by decide) width.property.2.1
  have hlow : w.toNat % 2 ^ width.val % 2 ^ (width.val - 1) =
      w.toNat % 2 ^ (width.val - 1) :=
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))
  have htest : UInt256.land w s ≠ ⟨0⟩ ↔
      2 ^ (width.val - 1) ≤ w.toNat % 2 ^ width.val := by
    have hand : (UInt256.land w s).toNat =
        (w.toNat.testBit (width.val - 1)).toNat * 2 ^ (width.val - 1) := by
      rw [uland_toNat, hs, Nat.and_two_pow]
    have hbit := testBit_eq_true_iff_half_le w.toNat (width.val - 1)
    rw [← hw] at hbit
    rw [← hbit]
    cases hb : w.toNat.testBit (width.val - 1) with
    | false =>
      have hz : UInt256.land w s = ⟨0⟩ := uint256_toNat_eq_zero (by simp [hand, hb])
      simp only [hz, ne_eq, not_true_eq_false, Bool.false_eq_true]
    | true =>
      have hnz : UInt256.land w s ≠ ⟨0⟩ := by
        intro hz
        have heq := congrArg UInt256.toNat hz
        rw [hand, hb] at heq
        simp only [Bool.toNat_true, one_mul, u256_zero_toNat] at heq
        omega
      exact iff_of_true hnz rfl
  rw [UInt256.signextend, if_pos ha]
  change (if UInt256.land w s ≠ ⟨0⟩ then UInt256.lor w (UInt256.sub _ s)
    else UInt256.land w (UInt256.sub s ⟨1⟩)) = _
  apply u256_inj
  rw [wordOfInt_normalizeSint_toNat]
  by_cases hhalf : 2 ^ (width.val - 1) ≤ w.toNat % 2 ^ width.val
  · rw [if_pos (htest.mpr hhalf), if_neg (by omega), u256_lor_toNat_exact]
    have hhigh : (UInt256.sub UInt256.size.toUInt256 s).toNat =
        UInt256.size - 2 ^ (width.val - 1) := by
      rw [usub_toNat_underflow (by change 0 < s.toNat; omega), hs]
      rfl
    rw [hhigh]
    change w.toNat ||| (2 ^ 256 - 2 ^ (width.val - 1)) = _
    rw [natLorHighMask w.toNat (width.val - 1) 256 w.val.isLt (by
      have := width.property; omega)]
    have hr : w.toNat % 2 ^ width.val % 2 ^ (width.val - 1) =
        w.toNat % 2 ^ width.val - 2 ^ (width.val - 1) := by
      rw [Nat.mod_eq_sub_mod hhalf, Nat.mod_eq_of_lt (by omega)]
    change w.toNat % 2 ^ (width.val - 1) + (UInt256.size - 2 ^ (width.val - 1)) = _
    omega
  · rw [if_neg (by intro h; exact hhalf (htest.mp h)), if_pos (by omega), uland_toNat,
      usub_toNat (by change 1 ≤ s.toNat; omega), hs]
    change Nat.land w.toNat (2 ^ (width.val - 1) - 1) = _
    rw [nat_land_mask_eq_mod]
    rw [Nat.mod_eq_of_lt (by omega)] at hlow
    exact hlow.symm

-- LIBRARY CANDIDATE: Reasoning.ABI, encode a signed cast using SIGNEXTEND.
theorem sintCastReturnEncoding (width : ABI.BitWidth) (a w : UInt256)
    (ha : a.toNat ≤ 31)
    (hsign : (UInt256.shiftLeft ⟨1⟩ (UInt256.add (UInt256.mul a ⟨8⟩) ⟨7⟩)).toNat =
      2 ^ (width.val - 1)) :
    encodeReturnValue? (.elem (.int (.sint width)))
      (.int (normalizeInt (.sint width) (Int.ofNat w.toNat))) =
        some (UInt256.toByteArray (UInt256.signextend a w)) := by
  rw [signextend_normalizeSint width a w ha hsign]
  exact sintReturnEncoding width _ (normalizeSint_bounds width _).1 (normalizeSint_bounds width _).2

-- LIBRARY CANDIDATE: Reasoning.WordArithmetic, signed casts ignore bits outside their width.
theorem normalizeSint_mask (width : ABI.BitWidth) (w mask : UInt256)
    (hmask : mask.toNat = 2 ^ width.val - 1) :
    normalizeInt (.sint width) (Int.ofNat (UInt256.land w mask).toNat) =
      normalizeInt (.sint width) (Int.ofNat w.toNat) := by
  have hm : (UInt256.land w mask).toNat = w.toNat % 2 ^ width.val := by
    rw [uland_toNat, hmask]
    change Nat.land w.toNat (2 ^ width.val - 1) = _
    exact nat_land_mask_eq_mod _ _
  simp only [normalizeInt, hm]
  have hres : Int.ofNat (w.toNat % 2 ^ width.val) % Int.ofNat (EVM.twoPow width.val) =
      Int.ofNat w.toNat % Int.ofNat (EVM.twoPow width.val) := by
    change Int.ofNat ((w.toNat % 2 ^ width.val) % 2 ^ width.val) =
      Int.ofNat (w.toNat % 2 ^ width.val)
    rw [Nat.mod_mod]
  rw [hres]

-- LIBRARY CANDIDATE: Reasoning.WordArithmetic, signed cleanup preserves the low-bit residue.
theorem wordOfInt_normalizeSint_mod (width : ABI.BitWidth) (w : UInt256) :
    (EVM.wordOfInt (normalizeInt (.sint width) (Int.ofNat w.toNat))).toNat % 2 ^ width.val =
      w.toNat % 2 ^ width.val := by
  rw [wordOfInt_normalizeSint_toNat]
  split
  · exact Nat.mod_mod _ _
  · have hmod : w.toNat % 2 ^ width.val < 2 ^ width.val := Nat.mod_lt _ (by positivity)
    have hwidth : 2 ^ width.val ≤ UInt256.size :=
      Nat.pow_le_pow_right (by decide) width.property.2.1
    have hdvd : 2 ^ width.val ∣ UInt256.size := Nat.pow_dvd_pow 2 width.property.2.1
    have hz : (UInt256.size - 2 ^ width.val) % 2 ^ width.val = 0 :=
      Nat.mod_eq_zero_of_dvd (Nat.dvd_sub hdvd (Nat.dvd_refl _))
    rw [show UInt256.size - (2 ^ width.val - w.toNat % 2 ^ width.val) =
      (UInt256.size - 2 ^ width.val) + w.toNat % 2 ^ width.val by omega,
      Nat.add_mod, hz, Nat.zero_add, Nat.mod_mod, Nat.mod_mod]

-- LIBRARY CANDIDATE: Reasoning.WordArithmetic, repeated SIGNEXTEND has no effect.
theorem signextend_idem (width : ABI.BitWidth) (a w : UInt256)
    (ha : a.toNat ≤ 31)
    (hsign : (UInt256.shiftLeft ⟨1⟩ (UInt256.add (UInt256.mul a ⟨8⟩) ⟨7⟩)).toNat =
      2 ^ (width.val - 1)) :
    UInt256.signextend a (UInt256.signextend a w) = UInt256.signextend a w := by
  rw [signextend_normalizeSint width a _ ha hsign, signextend_normalizeSint width a w ha hsign]
  congr 1
  have hr : Int.ofNat (EVM.wordOfInt (normalizeInt (.sint width) (Int.ofNat w.toNat))).toNat %
      Int.ofNat (EVM.twoPow width.val) = Int.ofNat w.toNat % Int.ofNat (EVM.twoPow width.val) := by
    change Int.ofNat ((EVM.wordOfInt (normalizeInt (.sint width) (Int.ofNat w.toNat))).toNat %
      2 ^ width.val) = Int.ofNat (w.toNat % 2 ^ width.val)
    rw [wordOfInt_normalizeSint_mod]
  rw [normalizeInt, hr]
  rfl

-- LIBRARY CANDIDATE: Reasoning.ABI, encode any normalized signed word.
theorem encodeABIValue_sintCast (width : ABI.BitWidth) (w : UInt256) :
    encodeABIValue? (.elem (.int (.sint width)))
      (.int (normalizeInt (.sint width) (Int.ofNat w.toNat))) =
      some (EVM.Word.toBytesBE (EVM.wordOfInt
        (normalizeInt (.sint width) (Int.ofNat w.toNat)))) := by
  have hbounds := normalizeSint_bounds width (Int.ofNat w.toNat)
  simp only [encodeABIValue?, encodeABIWord?, if_neg (Nat.ne_of_gt width.property.1),
    if_pos hbounds, bind, Option.bind]

end Benchmarks.UniswapV3.Pool


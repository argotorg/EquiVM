import Benchmarks.Dss.Vat.Common
import Benchmarks.Dss.Vat.Signed

namespace Benchmarks.Dss.Vat

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

/-! ## Shared definitions for `fold(bytes32,address,int256)` -/

abbrev foldIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4
abbrev foldUsrWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36
abbrev foldUsrMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (foldUsrWord I)
abbrev foldRateWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

theorem foldUsrMaskedWord_clean (I : ExecutionEnv) :
    UInt256.land (foldUsrMaskedWord I) solcAddrMask = foldUsrMaskedWord I := by
  unfold foldUsrMaskedWord
  rw [u256_land_comm solcAddrMask (foldUsrWord I)]
  exact solcAddrMask_clean (solcAddrMask_result_canonical (foldUsrWord I))

theorem u256_mul_zero_right (w : UInt256) : UInt256.mul w ⟨0⟩ = ⟨0⟩ := by
  apply u256_inj
  rw [u256_mul_toNat]
  simp

theorem u256_mul_zero_left (w : UInt256) : UInt256.mul ⟨0⟩ w = ⟨0⟩ := by
  rw [u256_mul_comm]
  exact u256_mul_zero_right w

theorem u256_div_zero_left (w : UInt256) : (⟨0⟩ : UInt256) / w = ⟨0⟩ := by
  apply u256_inj
  change (UInt256.div (⟨0⟩ : UInt256) w).toNat = (⟨0⟩ : UInt256).toNat
  rw [udiv_toNat]
  simp

theorem u256_sdiv_zero_left (w : UInt256) : UInt256.sdiv ⟨0⟩ w = ⟨0⟩ := by
  unfold UInt256.sdiv
  by_cases hw : EVM.twoPow 255 ≤ w.toNat
  · simp [u256_div_zero_left]
  · simp [u256_div_zero_left]

theorem u256_sdiv_high_low
    {prod rate : UInt256}
    (hprodHigh : EVM.twoPow 255 ≤ prod.toNat)
    (hrateLow : rate.toNat < EVM.twoPow 255) :
    UInt256.sdiv prod rate =
      { val := (UInt256.div (UInt256.abs prod) rate).val * (-1 : Fin UInt256.size) } := by
  unfold UInt256.sdiv
  rw [if_pos (by simpa [EVM.twoPow] using hprodHigh)]
  rw [if_neg (by simpa [EVM.twoPow] using not_le.mpr hrateLow)]
  rfl

theorem u256_div_toNat_eq_of_toNat {a b z : UInt256} {denom : Nat}
    (ha : a.toNat = denom * z.toNat)
    (hb : b.toNat = denom)
    (hdenomPos : 0 < denom) :
    (UInt256.div a b).toNat = z.toNat := by
  rw [udiv_toNat, ha, hb]
  exact Nat.mul_div_right z.toNat hdenomPos

theorem nat_mul_pred_mod {a M : Nat} (ha0 : 0 < a) (haM : a < M) :
    a * (M - 1) % M = M - a := by
  have hmod : a * (M - 1) = (a - 1) * M + (M - a) := by
    apply Nat.cast_injective (R := Int)
    have h1 : ((a - 1 : Nat) : Int) = (a : Int) - 1 := by omega
    have h2 : ((M - 1 : Nat) : Int) = (M : Int) - 1 := by omega
    have h3 : ((M - a : Nat) : Int) = (M : Int) - (a : Int) := by omega
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_mul, h1, h2, h3]
    ring
  rw [hmod, Nat.add_mod, Nat.mul_mod_left]
  simp [Nat.mod_eq_of_lt (by omega : M - a < M)]

theorem nat_sub_mul_mod {r a M : Nat} (hr0 : 0 < r) (ha0 : 0 < a)
    (hprod : r * a < M) :
    (M - r) * a % M = M - r * a := by
  have hrleM : r ≤ M := by nlinarith
  have hmod : (M - r) * a = (a - 1) * M + (M - r * a) := by
    apply Nat.cast_injective (R := Int)
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_mul]
    rw [Nat.cast_sub hrleM, Nat.cast_sub (by omega : 1 ≤ a),
      Nat.cast_sub (le_of_lt hprod)]
    rw [Nat.cast_mul]
    ring
  rw [hmod, Nat.add_mod, Nat.mul_mod_left]
  simp [Nat.mod_eq_of_lt (by
    have hp : 0 < r * a := Nat.mul_pos hr0 ha0
    omega : M - r * a < M)]

theorem int_neg_mul_bound_to_nat {a r : Nat}
    (h : -((2 : Int) ^ 255) ≤ Int.ofNat a * -Int.ofNat r) :
    r * a ≤ EVM.twoPow 255 := by
  have h' := h
  ring_nf at h'
  have hcastArt : ((a * r : Nat) : Int) ≤ (2 : Int) ^ 255 := by
    change Int.ofNat a * Int.ofNat r ≤ (2 : Int) ^ 255
    omega
  have hcast : ((r * a : Nat) : Int) ≤ (2 : Int) ^ 255 := by
    rw [Nat.mul_comm]
    exact hcastArt
  change r * a ≤ 2 ^ 255
  apply Int.ofNat_le.mp
  have hpow : ((2 ^ 255 : Nat) : Int) = (2 : Int) ^ 255 := by norm_num
  rw [hpow]
  exact hcast

theorem u256_size_eq_two_sign :
    UInt256.size = EVM.twoPow 255 + EVM.twoPow 255 := by
  native_decide

theorem u256_sign_lt_size : EVM.twoPow 255 < UInt256.size := by
  rw [u256_size_eq_two_sign]
  exact Nat.lt_add_of_pos_right (by
    change 0 < 2 ^ 255
    exact pow_pos (by decide : (0 : Nat) < 2) 255)

theorem fin_uint256_neg_one_val :
    ((-1 : Fin UInt256.size).val) = UInt256.size - 1 := by
  rw [Fin.val_neg]
  rw [if_neg]
  · rfl
  · intro hbad
    have hval := congrArg Fin.val hbad
    have hone : ((1 : Fin UInt256.size).val) = 1 := by
      show (Fin.ofNat UInt256.size 1).val = 1
      rw [Fin.ofNat]
      exact Nat.mod_eq_of_lt (by native_decide)
    rw [hone] at hval
    norm_num at hval

theorem fin_uint256_mul_neg_one_val {w : UInt256} (hpos : 0 < w.toNat) :
    (w.val * (-1 : Fin UInt256.size)).val = UInt256.size - w.toNat := by
  rw [Fin.val_mul, fin_uint256_neg_one_val]
  exact nat_mul_pred_mod hpos w.val.isLt

theorem fin_uint256_mul_neg_one_high {w : UInt256}
    (hpos : 0 < w.toNat) (hle : w.toNat ≤ EVM.twoPow 255) :
    EVM.twoPow 255 ≤ (w.val * (-1 : Fin UInt256.size)).val := by
  rw [fin_uint256_mul_neg_one_val (w := w) hpos]
  rw [u256_size_eq_two_sign]
  exact Nat.le_sub_of_add_le (Nat.add_le_add_left hle (EVM.twoPow 255))

theorem fin_uint256_mul_neg_one_val_low_contra {q art : UInt256}
    (hqLe : q.toNat ≤ EVM.twoPow 255)
    (hartLow : art.toNat < EVM.twoPow 255)
    (hartNe : art ≠ ⟨0⟩)
    (hnegVal : (q.val * (-1 : Fin UInt256.size)).val = art.toNat) : False := by
  by_cases hqZero : q = ⟨0⟩
  · have hartZero : art.toNat = 0 := by
      rw [← hnegVal]
      rw [hqZero]
      rfl
    exact hartNe (uint256_toNat_eq_zero hartZero)
  · have hqPos : 0 < q.toNat := by
      have hqNatNe : q.toNat ≠ 0 := by
        intro hz
        exact hqZero (uint256_toNat_eq_zero hz)
      exact Nat.pos_of_ne_zero hqNatNe
    have hartHigh : EVM.twoPow 255 ≤ art.toNat := by
      rw [← hnegVal]
      exact fin_uint256_mul_neg_one_high hqPos hqLe
    omega

theorem u256_abs_high_toNat {w : UInt256}
    (hhi : 2 ^ 255 ≤ w.toNat) (hpos : 0 < w.toNat) :
    (UInt256.abs w).toNat = UInt256.size - w.toNat := by
  cases w with
  | mk val =>
      change (UInt256.abs { val := val }).toNat = UInt256.size - val.val
      unfold UInt256.abs
      simp only [UInt256.toNat] at hhi hpos ⊢
      rw [if_pos hhi]
      change (val * (-1 : Fin UInt256.size)).val = UInt256.size - val.val
      exact fin_uint256_mul_neg_one_val (w := { val := val }) hpos

theorem fold_mul_word_guard_true_of_art_zero (I : ExecutionEnv) {art : UInt256}
    (hart : art = ⟨0⟩) :
    foldRateWord I = ⟨0⟩ ∨
      UInt256.eq (UInt256.sdiv (UInt256.mul (foldRateWord I) art)
        (foldRateWord I)) art ≠ ⟨0⟩ := by
  by_cases hrate : foldRateWord I = ⟨0⟩
  · exact Or.inl hrate
  · exact Or.inr (by
      rw [hart, u256_mul_zero_right, u256_sdiv_zero_left, u256_eq_refl]
      native_decide)

abbrev foldRateInt (I : ExecutionEnv) : Int :=
  if (foldRateWord I).toNat < EVM.twoPow 255 then
    Int.ofNat (foldRateWord I).toNat
  else
    Int.ofNat (foldRateWord I).toNat - Int.ofNat EVM.wordModulus

theorem foldRateInt_zero_of_word_zero (I : ExecutionEnv)
    (hword : foldRateWord I = ⟨0⟩) : foldRateInt I = 0 := by
  unfold foldRateInt
  rw [hword]
  rw [if_pos (by native_decide)]
  rfl

theorem foldRateInt_ne_zero_of_word_ne_zero (I : ExecutionEnv)
    (hword : foldRateWord I ≠ ⟨0⟩) : foldRateInt I ≠ 0 := by
  unfold foldRateInt
  by_cases hlow : (foldRateWord I).toNat < EVM.twoPow 255
  · rw [if_pos hlow]
    intro hzero
    have hnat : (foldRateWord I).toNat = 0 :=
      Nat.cast_eq_zero.mp hzero
    exact hword (by
      apply u256_inj
      simpa using hnat)
  · rw [if_neg hlow]
    intro hzero
    have hzero' :
        ((foldRateWord I).toNat : Int) - (EVM.wordModulus : Int) = 0 := by
      simpa using hzero
    have hltInt :
        ((foldRateWord I).toNat : Int) < (EVM.wordModulus : Int) := by
      exact_mod_cast (foldRateWord I).val.isLt
    have heqInt :
        ((foldRateWord I).toNat : Int) = (EVM.wordModulus : Int) := by
      omega
    omega

theorem foldRateInt_eq_of_low (I : ExecutionEnv)
    (hlow : (foldRateWord I).toNat < EVM.twoPow 255) :
    foldRateInt I = Int.ofNat (foldRateWord I).toNat := by
  unfold foldRateInt
  rw [if_pos hlow]

theorem foldRateInt_pos_of_low_ne (I : ExecutionEnv)
    (hlow : (foldRateWord I).toNat < EVM.twoPow 255)
    (hword : foldRateWord I ≠ ⟨0⟩) :
    0 < foldRateInt I := by
  rw [foldRateInt_eq_of_low I hlow]
  apply Int.natCast_pos.mpr
  exact (by
    have hneNat : (foldRateWord I).toNat ≠ 0 := by
      intro hzero
      exact hword (uint256_toNat_eq_zero hzero)
    exact Nat.pos_of_ne_zero hneNat)

theorem foldRateInt_eq_of_high (I : ExecutionEnv)
    (hhigh : EVM.twoPow 255 ≤ (foldRateWord I).toNat) :
    foldRateInt I =
      Int.ofNat (foldRateWord I).toNat - Int.ofNat EVM.wordModulus := by
  unfold foldRateInt
  rw [if_neg (by simpa [EVM.twoPow] using not_lt.mpr hhigh)]

theorem foldRateInt_neg_of_high (I : ExecutionEnv)
    (hhigh : EVM.twoPow 255 ≤ (foldRateWord I).toNat) :
    foldRateInt I < 0 := by
  rw [foldRateInt_eq_of_high I hhigh]
  have hlt : Int.ofNat (foldRateWord I).toNat < Int.ofNat EVM.wordModulus := by
    have hltNat : (foldRateWord I).toNat < EVM.wordModulus := by
      change (foldRateWord I).val.val < EVM.twoPow 256
      exact (foldRateWord I).val.isLt
    exact Int.ofNat_lt.mpr hltNat
  exact sub_neg.mpr hlt

theorem u256_toNat_lt_sign_of_slt_zero {w : UInt256}
    (hslt : UInt256.slt w ⟨0⟩ = ⟨0⟩) :
    w.toNat < EVM.twoPow 255 := by
  have hle := uintWordLeMaxInt256_of_slt_zero hslt
  have hltInt : (w.toNat : Int) < (2 : Int) ^ 255 := by
    have hmaxLt : maxInt256 < (2 : Int) ^ 255 := by
      unfold maxInt256
      omega
    exact lt_of_le_of_lt hle hmaxLt
  change w.toNat < 2 ^ 255
  exact Int.ofNat_lt.mp (by
    have hpow : ((2 ^ 255 : Nat) : Int) = (2 : Int) ^ 255 := by norm_num
    rw [hpow]
    exact hltInt)

theorem u256_slt_zero_ne_zero_of_high {w : UInt256}
    (hhi : EVM.twoPow 255 ≤ w.toNat) : UInt256.slt w ⟨0⟩ ≠ ⟨0⟩ := by
  have hcond : w.val.val ≥ 2 ^ 255 := by
    simpa [EVM.twoPow, UInt256.toNat] using hhi
  unfold UInt256.slt UInt256.sltBool UInt256.fromBool Bool.toUInt256
  simp only [UInt256.toNat]
  rw [if_pos hcond]
  rw [if_neg (by native_decide : ¬ ((0 : Fin UInt256.size).val ≥ 2 ^ 255))]
  native_decide

theorem foldRateInt_mod_word (I : ExecutionEnv) :
    foldRateInt I % (Int.ofNat EVM.wordModulus) =
      Int.ofNat (foldRateWord I).toNat := by
  have hltMod :
      (Int.ofNat (foldRateWord I).toNat) < Int.ofNat EVM.wordModulus := by
    have hltNat : (foldRateWord I).toNat < EVM.wordModulus := by
      change (foldRateWord I).val.val < EVM.twoPow 256
      exact (foldRateWord I).val.isLt
    exact Int.ofNat_lt.mpr hltNat
  have hbase :
      (Int.ofNat (foldRateWord I).toNat) % (Int.ofNat EVM.wordModulus) =
        Int.ofNat (foldRateWord I).toNat :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) hltMod
  unfold foldRateInt
  split
  · exact hbase
  · rw [← Int.emod_eq_sub_self_emod]
    exact hbase

theorem fold_mul_word_guard_true_of_range_pos
    (I : ExecutionEnv) {art : UInt256}
    (hrateLow : (foldRateWord I).toNat < EVM.twoPow 255)
    (hrateWordNe : foldRateWord I ≠ ⟨0⟩)
    (hprodHi :
      Int.ofNat art.toNat * foldRateInt I < (2 : Int) ^ 255) :
    foldRateWord I = ⟨0⟩ ∨
      UInt256.eq (UInt256.sdiv (UInt256.mul (foldRateWord I) art)
        (foldRateWord I)) art ≠ ⟨0⟩ := by
  right
  have hrateNatPos : 0 < (foldRateWord I).toNat := by
    have hneNat : (foldRateWord I).toNat ≠ 0 := by
      intro hzero
      exact hrateWordNe (uint256_toNat_eq_zero hzero)
    exact Nat.pos_of_ne_zero hneNat
  have hprodInt :
      (Int.ofNat ((foldRateWord I).toNat * art.toNat)) < (2 : Int) ^ 255 := by
    have hrateInt :
        foldRateInt I = Int.ofNat (foldRateWord I).toNat := by
      unfold foldRateInt
      rw [if_pos hrateLow]
    have h := hprodHi
    rw [hrateInt] at h
    change (((foldRateWord I).toNat * art.toNat : Nat) : Int) < (2 : Int) ^ 255
    rw [Nat.mul_comm]
    exact h
  have hprodNatSign :
      (foldRateWord I).toNat * art.toNat < EVM.twoPow 255 := by
    change (foldRateWord I).toNat * art.toNat < 2 ^ 255
    apply Int.ofNat_lt.mp
    have hpow : ((2 ^ 255 : Nat) : Int) = (2 : Int) ^ 255 := by
      norm_num
    rw [hpow]
    exact hprodInt
  have hprodNatSize :
      (foldRateWord I).toNat * art.toNat < UInt256.size := by
    have hsignSize : EVM.twoPow 255 < UInt256.size := by
      norm_num [EVM.twoPow, UInt256.size]
    omega
  have hmulToNat :
      (UInt256.mul (foldRateWord I) art).toNat =
        (foldRateWord I).toNat * art.toNat := by
    rw [u256_mul_toNat]
    exact Nat.mod_eq_of_lt hprodNatSize
  have hmulLow :
      ¬ EVM.twoPow 255 ≤ (UInt256.mul (foldRateWord I) art).toNat := by
    rw [hmulToNat]
    omega
  have hrateLowNot :
      ¬ EVM.twoPow 255 ≤ (foldRateWord I).toNat := by
    omega
  have hsdiv :
      UInt256.sdiv (UInt256.mul (foldRateWord I) art) (foldRateWord I) = art := by
    unfold UInt256.sdiv
    rw [if_neg]
    · rw [if_neg]
      · apply u256_inj
        change (UInt256.div (UInt256.mul (foldRateWord I) art)
          (foldRateWord I)).toNat = art.toNat
        rw [udiv_toNat, hmulToNat]
        exact Nat.mul_div_right art.toNat hrateNatPos
      · simpa [EVM.twoPow] using hrateLowNot
    · simpa [EVM.twoPow] using hmulLow
  rw [hsdiv, u256_eq_refl]
  native_decide

theorem fold_mul_word_range_hi_of_guard_pos
    (I : ExecutionEnv) {art : UInt256}
    (hrateLow : (foldRateWord I).toNat < EVM.twoPow 255)
    (hartLow : art.toNat < EVM.twoPow 255)
    (hartNe : art ≠ ⟨0⟩)
    (hsdiv :
      UInt256.sdiv (UInt256.mul (foldRateWord I) art) (foldRateWord I) = art) :
    (UInt256.mul (foldRateWord I) art).toNat < EVM.twoPow 255 := by
  by_contra hnot
  have hprodHigh : EVM.twoPow 255 ≤ (UInt256.mul (foldRateWord I) art).toNat :=
    not_lt.mp hnot
  have hprodPos : 0 < (UInt256.mul (foldRateWord I) art).toNat := by
    have hpow : 0 < EVM.twoPow 255 := by
      change 0 < 2 ^ 255
      exact pow_pos (by decide : (0 : Nat) < 2) 255
    exact lt_of_lt_of_le hpow hprodHigh
  let q := UInt256.div (UInt256.abs (UInt256.mul (foldRateWord I) art))
    (foldRateWord I)
  have hqLe : q.toNat ≤ EVM.twoPow 255 := by
    dsimp [q]
    rw [udiv_toNat]
    have habs :
        (UInt256.abs (UInt256.mul (foldRateWord I) art)).toNat =
          UInt256.size - (UInt256.mul (foldRateWord I) art).toNat :=
      u256_abs_high_toNat hprodHigh hprodPos
    rw [habs]
    have hsub :
        UInt256.size - (UInt256.mul (foldRateWord I) art).toNat ≤
          EVM.twoPow 255 := by
      rw [u256_size_eq_two_sign]
      omega
    exact le_trans (Nat.div_le_self _ _) hsub
  have hs := u256_sdiv_high_low (prod := UInt256.mul (foldRateWord I) art)
    (rate := foldRateWord I) hprodHigh hrateLow
  rw [hs] at hsdiv
  cases art with
  | mk aval =>
      dsimp [UInt256.toNat] at hartLow
      dsimp [q] at hqLe hsdiv
      generalize hq :
        UInt256.div (UInt256.abs (UInt256.mul (foldRateWord I) { val := aval }))
            (foldRateWord I) = qword at hqLe hsdiv
      cases qword with
      | mk qval =>
          have hnegVal : (qval * (-1 : Fin UInt256.size)).val = aval.val := by
            injection hsdiv with hv
            exact congrArg Fin.val hv
          exact fin_uint256_mul_neg_one_val_low_contra
            (q := { val := qval }) (art := { val := aval }) hqLe hartLow
            hartNe hnegVal

set_option maxHeartbeats 0 in
theorem fold_mul_word_product_hi_of_guard_pos
    (I : ExecutionEnv) {art : UInt256}
    (hrateLow : (foldRateWord I).toNat < EVM.twoPow 255)
    (hartLow : art.toNat < EVM.twoPow 255)
    (hartNe : art ≠ ⟨0⟩)
    (hsdiv :
      UInt256.sdiv (UInt256.mul (foldRateWord I) art) (foldRateWord I) = art) :
    Int.ofNat art.toNat * foldRateInt I < (2 : Int) ^ 255 := by
  have hprodLow : (UInt256.mul (foldRateWord I) art).toNat < EVM.twoPow 255 :=
    fold_mul_word_range_hi_of_guard_pos I hrateLow hartLow hartNe hsdiv
  have hprodLowNot :
      ¬ EVM.twoPow 255 ≤ (UInt256.mul (foldRateWord I) art).toNat := by
    omega
  have hrateLowNot : ¬ EVM.twoPow 255 ≤ (foldRateWord I).toNat := by
    omega
  have hsdivEq :
      UInt256.div (UInt256.mul (foldRateWord I) art) (foldRateWord I) = art := by
    unfold UInt256.sdiv at hsdiv
    rw [if_neg (by simpa [EVM.twoPow] using hprodLowNot)] at hsdiv
    rw [if_neg (by simpa [EVM.twoPow] using hrateLowNot)] at hsdiv
    exact hsdiv
  have hdivNat :
      (UInt256.mul (foldRateWord I) art).toNat / (foldRateWord I).toNat =
        art.toNat := by
    have h := congrArg UInt256.toNat hsdivEq
    simpa [udiv_toNat] using h
  let P := (foldRateWord I).toNat * art.toNat
  have hmulMod : (UInt256.mul (foldRateWord I) art).toNat = P % UInt256.size := by
    dsimp [P]
    rw [u256_mul_toNat]
  have hleDiv :
      art.toNat ≤
        (UInt256.mul (foldRateWord I) art).toNat / (foldRateWord I).toNat := by
    rw [hdivNat]
  have hPLeMod : P ≤ P % UInt256.size := by
    dsimp [P]
    rw [← hmulMod]
    have hle := Nat.mul_le_of_le_div (foldRateWord I).toNat art.toNat
      (UInt256.mul (foldRateWord I) art).toNat hleDiv
    simpa [Nat.mul_comm] using hle
  have hPEqMod : P = P % UInt256.size :=
    le_antisymm hPLeMod (Nat.mod_le P UInt256.size)
  have hPLtSign : P < EVM.twoPow 255 := by
    rw [hPEqMod]
    rw [← hmulMod]
    exact hprodLow
  dsimp [P] at hPLtSign
  rw [foldRateInt_eq_of_low I hrateLow]
  have hcast :
      ((art.toNat * (foldRateWord I).toNat : Nat) : Int) < (2 : Int) ^ 255 := by
    rw [Nat.mul_comm]
    exact_mod_cast (by simpa [EVM.twoPow] using hPLtSign)
  simpa using hcast

theorem fold_mul_word_high_toNat_of_range_neg
    (I : ExecutionEnv) {art : UInt256}
    (hrateHigh : EVM.twoPow 255 ≤ (foldRateWord I).toNat)
    (hartNe : art ≠ ⟨0⟩)
    (hprodLo :
      -((2 : Int) ^ 255) ≤ Int.ofNat art.toNat * foldRateInt I) :
    (UInt256.mul (foldRateWord I) art).toNat =
      UInt256.size - ((UInt256.size - (foldRateWord I).toNat) * art.toNat) := by
  let rabs := UInt256.size - (foldRateWord I).toNat
  have hrateInt : foldRateInt I = - Int.ofNat rabs := by
    unfold foldRateInt
    rw [if_neg (by simpa [EVM.twoPow] using not_lt.mpr hrateHigh)]
    dsimp [rabs]
    have hword : EVM.wordModulus = UInt256.size := by rfl
    rw [hword]
    have hle : (foldRateWord I).toNat ≤ UInt256.size :=
      Nat.le_of_lt (foldRateWord I).val.isLt
    rw [Nat.cast_sub hle]
    omega
  have hrabsPos : 0 < rabs := by
    dsimp [rabs]
    have hlt : (foldRateWord I).toNat < UInt256.size := (foldRateWord I).val.isLt
    omega
  have hartPos : 0 < art.toNat := by
    have hneNat : art.toNat ≠ 0 := by
      intro hz
      exact hartNe (uint256_toNat_eq_zero hz)
    exact Nat.pos_of_ne_zero hneNat
  have hprodLeSign : rabs * art.toNat ≤ EVM.twoPow 255 := by
    have h := hprodLo
    rw [hrateInt] at h
    exact int_neg_mul_bound_to_nat h
  have hprodBound : rabs * art.toNat < UInt256.size := by
    exact lt_of_le_of_lt hprodLeSign u256_sign_lt_size
  rw [u256_mul_toNat]
  change (foldRateWord I).toNat * art.toNat % UInt256.size =
    UInt256.size - rabs * art.toNat
  have hrateNat : (foldRateWord I).toNat = UInt256.size - rabs := by
    dsimp [rabs]
    omega
  rw [hrateNat]
  exact nat_sub_mul_mod hrabsPos hartPos hprodBound

theorem fold_mul_word_guard_true_of_range_neg
    (I : ExecutionEnv) {art : UInt256}
    (hrateHigh : EVM.twoPow 255 ≤ (foldRateWord I).toNat)
    (hartNe : art ≠ ⟨0⟩)
    (hprodLo :
      -((2 : Int) ^ 255) ≤ Int.ofNat art.toNat * foldRateInt I) :
    foldRateWord I = ⟨0⟩ ∨
      UInt256.eq (UInt256.sdiv (UInt256.mul (foldRateWord I) art)
        (foldRateWord I)) art ≠ ⟨0⟩ := by
  right
  let rabs := UInt256.size - (foldRateWord I).toNat
  let p := rabs * art.toNat
  have hpowPos : 0 < EVM.twoPow 255 := by
    change 0 < 2 ^ 255
    exact pow_pos (by decide : (0 : Nat) < 2) 255
  have hratePos : 0 < (foldRateWord I).toNat :=
    lt_of_lt_of_le hpowPos hrateHigh
  have hrabsPos : 0 < rabs := by
    dsimp [rabs]
    have hlt : (foldRateWord I).toNat < UInt256.size := (foldRateWord I).val.isLt
    omega
  have hartPos : 0 < art.toNat := by
    have hneNat : art.toNat ≠ 0 := by
      intro hz
      exact hartNe (uint256_toNat_eq_zero hz)
    exact Nat.pos_of_ne_zero hneNat
  have hrateInt : foldRateInt I = - Int.ofNat rabs := by
    unfold foldRateInt
    rw [if_neg (by simpa [EVM.twoPow] using not_lt.mpr hrateHigh)]
    dsimp [rabs]
    have hword : EVM.wordModulus = UInt256.size := by rfl
    rw [hword]
    have hle : (foldRateWord I).toNat ≤ UInt256.size :=
      Nat.le_of_lt (foldRateWord I).val.isLt
    rw [Nat.cast_sub hle]
    omega
  have hprodLeSign : p ≤ EVM.twoPow 255 := by
    dsimp [p]
    have h := hprodLo
    rw [hrateInt] at h
    exact int_neg_mul_bound_to_nat h
  have hprodBound : p < UInt256.size :=
    lt_of_le_of_lt hprodLeSign u256_sign_lt_size
  have hprodToNat : (UInt256.mul (foldRateWord I) art).toNat = UInt256.size - p := by
    dsimp [p, rabs]
    exact fold_mul_word_high_toNat_of_range_neg I hrateHigh hartNe hprodLo
  have hprodHigh : EVM.twoPow 255 ≤ (UInt256.mul (foldRateWord I) art).toNat := by
    rw [hprodToNat, u256_size_eq_two_sign]
    omega
  have hprodPos : 0 < (UInt256.mul (foldRateWord I) art).toNat :=
    lt_of_lt_of_le hpowPos hprodHigh
  have hAbsRateToNat : (UInt256.abs (foldRateWord I)).toNat = rabs := by
    dsimp [rabs]
    exact u256_abs_high_toNat (by simpa [EVM.twoPow] using hrateHigh) hratePos
  have hAbsProdToNat :
      (UInt256.abs (UInt256.mul (foldRateWord I) art)).toNat = p := by
    rw [u256_abs_high_toNat (by simpa [EVM.twoPow] using hprodHigh) hprodPos]
    rw [hprodToNat]
    exact Nat.sub_sub_self (le_of_lt hprodBound)
  have hsdiv :
      UInt256.sdiv (UInt256.mul (foldRateWord I) art) (foldRateWord I) = art := by
    unfold UInt256.sdiv
    rw [if_pos (by simpa [EVM.twoPow] using hprodHigh)]
    rw [if_pos (by simpa [EVM.twoPow] using hrateHigh)]
    apply u256_inj
    change (UInt256.div (UInt256.abs (UInt256.mul (foldRateWord I) art))
      (UInt256.abs (foldRateWord I))).toNat = art.toNat
    apply u256_div_toNat_eq_of_toNat (denom := rabs)
    · rw [hAbsProdToNat]
    · exact hAbsRateToNat
    · exact hrabsPos
  rw [hsdiv, u256_eq_refl]
  native_decide

theorem u256_abs_div_eq_bound_to_sign {rate prod art : UInt256} {rabs : Nat}
    (hrabs : (UInt256.abs rate).toNat = rabs)
    (hprodHigh : EVM.twoPow 255 ≤ prod.toNat)
    (hprodPos : 0 < prod.toNat)
    (hdiv : UInt256.div (UInt256.abs prod) (UInt256.abs rate) = art) :
    rabs * art.toNat ≤ EVM.twoPow 255 := by
  have hAbsProdToNat : (UInt256.abs prod).toNat = UInt256.size - prod.toNat :=
    u256_abs_high_toNat hprodHigh hprodPos
  have hdivNat : (UInt256.abs prod).toNat / (UInt256.abs rate).toNat = art.toNat := by
    have h := congrArg UInt256.toNat hdiv
    simpa [udiv_toNat] using h
  have hleDiv : art.toNat ≤ (UInt256.abs prod).toNat / (UInt256.abs rate).toNat := by
    rw [hdivNat]
  have hpLeAbs : rabs * art.toNat ≤ (UInt256.abs prod).toNat := by
    have hle := Nat.mul_le_of_le_div (UInt256.abs rate).toNat art.toNat
      (UInt256.abs prod).toNat hleDiv
    rw [hrabs] at hle
    simpa [Nat.mul_comm] using hle
  have hAbsLe : (UInt256.abs prod).toNat ≤ EVM.twoPow 255 := by
    rw [hAbsProdToNat, u256_size_eq_two_sign]
    omega
  exact le_trans hpLeAbs hAbsLe

set_option maxHeartbeats 0 in
theorem fold_mul_word_neg_rate_low_product_contra
    (I : ExecutionEnv) {art : UInt256}
    (hrateHigh : EVM.twoPow 255 ≤ (foldRateWord I).toNat)
    (hprodLow : (UInt256.mul (foldRateWord I) art).toNat < EVM.twoPow 255)
    (hartLow : art.toNat < EVM.twoPow 255)
    (hartNe : art ≠ ⟨0⟩)
    (hsdiv :
      UInt256.sdiv (UInt256.mul (foldRateWord I) art) (foldRateWord I) = art) :
    False := by
  have hrateHighIf : 2 ^ 255 ≤ (foldRateWord I).toNat := by
    simpa [EVM.twoPow] using hrateHigh
  have hprodHighNot : ¬ 2 ^ 255 ≤ (UInt256.mul (foldRateWord I) art).toNat := by
    simpa [EVM.twoPow] using not_le.mpr hprodLow
  have hs := hsdiv
  unfold UInt256.sdiv at hs
  rw [if_neg hprodHighNot] at hs
  rw [if_pos hrateHighIf] at hs
  let q := (UInt256.mul (foldRateWord I) art) / (UInt256.abs (foldRateWord I))
  have hqLe : q.toNat ≤ EVM.twoPow 255 := by
    dsimp [q]
    change (UInt256.div (UInt256.mul (foldRateWord I) art)
      (UInt256.abs (foldRateWord I))).toNat ≤ EVM.twoPow 255
    rw [udiv_toNat]
    exact le_trans (Nat.div_le_self _ _) (le_of_lt hprodLow)
  cases art with
  | mk aval =>
      dsimp [UInt256.toNat] at hartLow
      dsimp [q] at hqLe hs
      generalize hqwordEq :
        ((UInt256.mul (foldRateWord I) { val := aval }) /
          (UInt256.abs (foldRateWord I))) = qword at hqLe hs
      cases qword with
      | mk qval =>
          have hnegVal : (qval * (-1 : Fin UInt256.size)).val = aval.val := by
            injection hs with hv
            exact congrArg Fin.val hv
          exact fin_uint256_mul_neg_one_val_low_contra
            (q := { val := qval }) (art := { val := aval }) hqLe hartLow
            hartNe hnegVal

set_option maxHeartbeats 0 in
theorem fold_mul_word_product_lo_of_guard_neg
    (I : ExecutionEnv) {art : UInt256}
    (hrateHigh : EVM.twoPow 255 ≤ (foldRateWord I).toNat)
    (hartLow : art.toNat < EVM.twoPow 255)
    (hartNe : art ≠ ⟨0⟩)
    (hsdiv :
      UInt256.sdiv (UInt256.mul (foldRateWord I) art) (foldRateWord I) = art) :
    -((2 : Int) ^ 255) ≤ Int.ofNat art.toNat * foldRateInt I := by
  let rabs := UInt256.size - (foldRateWord I).toNat
  let prod := UInt256.mul (foldRateWord I) art
  have hpowPos : 0 < EVM.twoPow 255 := by
    change 0 < 2 ^ 255
    exact pow_pos (by decide : (0 : Nat) < 2) 255
  have hratePos : 0 < (foldRateWord I).toNat :=
    lt_of_lt_of_le hpowPos hrateHigh
  have hrateInt : foldRateInt I = - Int.ofNat rabs := by
    unfold foldRateInt
    rw [if_neg (by simpa [EVM.twoPow] using not_lt.mpr hrateHigh)]
    dsimp [rabs]
    have hword : EVM.wordModulus = UInt256.size := by rfl
    rw [hword]
    have hle : (foldRateWord I).toNat ≤ UInt256.size :=
      Nat.le_of_lt (foldRateWord I).val.isLt
    rw [Nat.cast_sub hle]
    omega
  have hAbsRateToNat : (UInt256.abs (foldRateWord I)).toNat = rabs := by
    dsimp [rabs]
    exact u256_abs_high_toNat (by simpa [EVM.twoPow] using hrateHigh) hratePos
  have hprodHigh : EVM.twoPow 255 ≤ prod.toNat := by
    by_contra hnot
    have hprodLow : prod.toNat < EVM.twoPow 255 := by
      omega
    exact fold_mul_word_neg_rate_low_product_contra I hrateHigh
      (by simpa [prod] using hprodLow) hartLow hartNe
      (by simpa [prod] using hsdiv)
  have hprodPos : 0 < prod.toNat :=
    lt_of_lt_of_le hpowPos hprodHigh
  have hrateHighIf : 2 ^ 255 ≤ (foldRateWord I).toNat := by
    simpa [EVM.twoPow] using hrateHigh
  have hsdivEq :
      UInt256.div (UInt256.abs prod) (UInt256.abs (foldRateWord I)) = art := by
    unfold UInt256.sdiv at hsdiv
    rw [if_pos (by simpa [EVM.twoPow, prod] using hprodHigh)] at hsdiv
    rw [if_pos hrateHighIf] at hsdiv
    simpa [prod] using hsdiv
  have hpLeSign : rabs * art.toNat ≤ EVM.twoPow 255 :=
    u256_abs_div_eq_bound_to_sign (rate := foldRateWord I) (prod := prod)
      (art := art) hAbsRateToNat hprodHigh hprodPos hsdivEq
  rw [hrateInt]
  have hp : ((rabs * art.toNat : Nat) : Int) ≤ (2 : Int) ^ 255 := by
    exact_mod_cast (by simpa [EVM.twoPow] using hpLeSign)
  have hmul :
      Int.ofNat art.toNat * -Int.ofNat rabs =
        -((rabs * art.toNat : Nat) : Int) := by
    calc
      Int.ofNat art.toNat * -Int.ofNat rabs =
          -(Int.ofNat art.toNat * Int.ofNat rabs) := by ring
      _ = -((art.toNat * rabs : Nat) : Int) := by
          exact congrArg Neg.neg (Nat.cast_mul art.toNat rabs).symm
      _ = -((rabs * art.toNat : Nat) : Int) := by rw [Nat.mul_comm]
  rw [hmul]
  omega

set_option maxHeartbeats 0 in
theorem fold_mul_word_product_range_of_guard
    (I : ExecutionEnv) {art : UInt256}
    (hartLow : art.toNat < EVM.twoPow 255)
    (hsdiv :
      UInt256.sdiv (UInt256.mul (foldRateWord I) art) (foldRateWord I) = art) :
    -((2 : Int) ^ 255) ≤ Int.ofNat art.toNat * foldRateInt I ∧
      Int.ofNat art.toNat * foldRateInt I < (2 : Int) ^ 255 := by
  by_cases hrateZero : foldRateWord I = ⟨0⟩
  · have hrateIntZero := foldRateInt_zero_of_word_zero I hrateZero
    constructor <;> rw [hrateIntZero] <;> norm_num
  · constructor
    · by_cases hrateLow : (foldRateWord I).toNat < EVM.twoPow 255
      · have hratePos := foldRateInt_pos_of_low_ne I hrateLow hrateZero
        have hsignPos : 0 < (2 : Int) ^ 255 := by norm_num
        have hartNonneg : 0 ≤ Int.ofNat art.toNat := Int.natCast_nonneg _
        nlinarith
      · by_cases hartZero : art = ⟨0⟩
        · rw [hartZero]
          norm_num
        · exact fold_mul_word_product_lo_of_guard_neg I (not_lt.mp hrateLow)
            hartLow hartZero hsdiv
    · by_cases hrateLow : (foldRateWord I).toNat < EVM.twoPow 255
      · by_cases hartZero : art = ⟨0⟩
        · rw [hartZero]
          norm_num
        · exact fold_mul_word_product_hi_of_guard_pos I hrateLow hartLow hartZero
            hsdiv
      · have hrateNeg := foldRateInt_neg_of_high I (not_lt.mp hrateLow)
        have hsignPos : 0 < (2 : Int) ^ 255 := by norm_num
        have hartNonneg : 0 ≤ Int.ofNat art.toNat := Int.natCast_nonneg _
        nlinarith

theorem int_eq_signed_word_of_range_mod {i : Int} {w : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ i)
    (hhi : i < (2 : Int) ^ 255)
    (hmod : i % (Int.ofNat EVM.wordModulus) = Int.ofNat w.toNat) :
    i =
      (if w.toNat < EVM.twoPow 255 then
        Int.ofNat w.toNat
      else
        Int.ofNat w.toNat - Int.ofNat EVM.wordModulus) := by
  have hsignLtM : (2 : Int) ^ 255 < Int.ofNat EVM.wordModulus := by
    norm_num [EVM.wordModulus, EVM.twoPow]
  by_cases hnonneg : 0 ≤ i
  · have hiM : i < Int.ofNat EVM.wordModulus := lt_trans hhi hsignLtM
    have hi : i = Int.ofNat w.toNat := by
      rw [Int.emod_eq_of_lt hnonneg hiM] at hmod
      exact hmod
    rw [hi]
    have hlow : w.toNat < EVM.twoPow 255 := by
      apply Int.ofNat_lt.mp
      have hpow : ((EVM.twoPow 255 : Nat) : Int) = (2 : Int) ^ 255 := by
        norm_num [EVM.twoPow]
      rw [hpow]
      simpa [hi] using hhi
    rw [if_pos hlow]
  · have hneg : i < 0 := not_le.mp hnonneg
    have hshiftNonneg : 0 ≤ i + Int.ofNat EVM.wordModulus := by
      have hloM : -Int.ofNat EVM.wordModulus < i := by
        have h : -Int.ofNat EVM.wordModulus < -((2 : Int) ^ 255) := by
          norm_num [EVM.wordModulus, EVM.twoPow]
        exact lt_of_lt_of_le h hlo
      omega
    have hshiftLt : i + Int.ofNat EVM.wordModulus < Int.ofNat EVM.wordModulus := by
      omega
    have hmodShift :
        i % Int.ofNat EVM.wordModulus = i + Int.ofNat EVM.wordModulus := by
      rw [Int.emod_eq_add_self_emod]
      exact Int.emod_eq_of_lt hshiftNonneg hshiftLt
    have hwi : Int.ofNat w.toNat = i + Int.ofNat EVM.wordModulus := by
      rw [hmodShift] at hmod
      exact hmod.symm
    have hhigh : ¬ w.toNat < EVM.twoPow 255 := by
      intro hlow
      have hwlt : Int.ofNat w.toNat < (2 : Int) ^ 255 := by
        exact_mod_cast (by simpa [EVM.twoPow] using hlow)
      have hwge : (2 : Int) ^ 255 ≤ Int.ofNat w.toNat := by
        rw [hwi]
        have hM :
            Int.ofNat EVM.wordModulus = (2 : Int) ^ 255 + (2 : Int) ^ 255 := by
          norm_num [EVM.wordModulus, EVM.twoPow]
        rw [hM]
        omega
      omega
    rw [if_neg hhigh]
    omega

theorem int_nonneg_of_word_slt_zero
    {i : Int} {w : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ i)
    (hhi : i < (2 : Int) ^ 255)
    (hmod : i % (Int.ofNat EVM.wordModulus) = Int.ofNat w.toNat)
    (hslt : UInt256.slt w ⟨0⟩ = ⟨0⟩) : 0 ≤ i := by
  have hsigned := int_eq_signed_word_of_range_mod hlo hhi hmod
  rw [hsigned]
  exact slt_zero_eq_zero_to_nonneg w hslt

theorem int_nonpos_of_word_sgt_zero
    {i : Int} {w : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ i)
    (hhi : i < (2 : Int) ^ 255)
    (hmod : i % (Int.ofNat EVM.wordModulus) = Int.ofNat w.toNat)
    (hsgt : UInt256.sgt w ⟨0⟩ = ⟨0⟩) : i ≤ 0 := by
  have hsigned := int_eq_signed_word_of_range_mod hlo hhi hmod
  rw [hsigned]
  exact sgt_zero_eq_zero_to_nonpos w hsgt

theorem int_neg_of_word_slt_ne_zero
    {i : Int} {w : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ i)
    (hhi : i < (2 : Int) ^ 255)
    (hmod : i % (Int.ofNat EVM.wordModulus) = Int.ofNat w.toNat)
    (hslt : UInt256.slt w ⟨0⟩ ≠ ⟨0⟩) : i < 0 := by
  have hsigned := int_eq_signed_word_of_range_mod hlo hhi hmod
  rw [hsigned]
  exact slt_zero_ne_zero_to_neg w hslt

theorem int_pos_of_word_sgt_ne_zero
    {i : Int} {w : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ i)
    (hhi : i < (2 : Int) ^ 255)
    (hmod : i % (Int.ofNat EVM.wordModulus) = Int.ofNat w.toNat)
    (hsgt : UInt256.sgt w ⟨0⟩ ≠ ⟨0⟩) : 0 < i := by
  have hsigned := int_eq_signed_word_of_range_mod hlo hhi hmod
  rw [hsigned]
  exact sgt_zero_ne_zero_to_pos w hsgt

theorem signedAddGuardNegCond_of_word
    {i : Int} {word old new : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ i)
    (hhi : i < (2 : Int) ^ 255)
    (hmod : i % (Int.ofNat EVM.wordModulus) = Int.ofNat word.toNat)
    (hneg :
      UInt256.slt word ⟨0⟩ = ⟨0⟩ ∨ UInt256.gt new old = ⟨0⟩) :
    0 ≤ i ∨ new.toNat ≤ old.toNat := by
  cases hneg with
  | inl hslt => exact Or.inl (int_nonneg_of_word_slt_zero hlo hhi hmod hslt)
  | inr hgt => exact Or.inr (ugt_eq_zero_to_le hgt)

theorem signedAddGuardPosCond_of_word
    {i : Int} {word old new : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ i)
    (hhi : i < (2 : Int) ^ 255)
    (hmod : i % (Int.ofNat EVM.wordModulus) = Int.ofNat word.toNat)
    (hpos :
      UInt256.sgt word ⟨0⟩ = ⟨0⟩ ∨ UInt256.lt new old = ⟨0⟩) :
    i ≤ 0 ∨ old.toNat ≤ new.toNat := by
  cases hpos with
  | inl hsgt => exact Or.inl (int_nonpos_of_word_sgt_zero hlo hhi hmod hsgt)
  | inr hlt => exact Or.inr (ult_eq_zero_to_le hlt)

theorem signedAddGuardNegFalseCond_of_word
    {i : Int} {word old new : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ i)
    (hhi : i < (2 : Int) ^ 255)
    (hmod : i % (Int.ofNat EVM.wordModulus) = Int.ofNat word.toNat)
    (hnegFail :
      ¬ (UInt256.slt word ⟨0⟩ = ⟨0⟩ ∨ UInt256.gt new old = ⟨0⟩)) :
    i < 0 ∧ old.toNat < new.toNat := by
  constructor
  · exact int_neg_of_word_slt_ne_zero hlo hhi hmod (by
      intro hslt
      exact hnegFail (Or.inl hslt))
  · exact ugt_ne_zero_to_gt (by
      intro hgt
      exact hnegFail (Or.inr hgt))

theorem signedAddGuardPosFalseCond_of_word
    {i : Int} {word old new : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ i)
    (hhi : i < (2 : Int) ^ 255)
    (hmod : i % (Int.ofNat EVM.wordModulus) = Int.ofNat word.toNat)
    (hposFail :
      ¬ (UInt256.sgt word ⟨0⟩ = ⟨0⟩ ∨ UInt256.lt new old = ⟨0⟩)) :
    0 < i ∧ new.toNat < old.toNat := by
  constructor
  · exact int_pos_of_word_sgt_ne_zero hlo hhi hmod (by
      intro hsgt
      exact hposFail (Or.inl hsgt))
  · exact ult_ne_zero_to_lt (by
      intro hlt
      exact hposFail (Or.inr hlt))

abbrev foldIlkBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32
abbrev foldIlkValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (foldIlkBytes I)
abbrev foldUsrValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (foldUsrWord I).toNat)
abbrev foldRateValue (I : ExecutionEnv) : Value :=
  .int (foldRateInt I)
abbrev foldStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "i" (foldIlkValue I)).insert "u" (foldUsrValue I)).insert
    "rate" (foldRateValue I)
abbrev foldStoreRateNew (I : ExecutionEnv) (rateNew : UInt256) : Store :=
  (foldStore I).insert "rateNew" (.int (Int.ofNat rateNew.toNat))
abbrev foldStoreRad (I : ExecutionEnv) (rateNew : UInt256) (rad : Int) : Store :=
  (foldStoreRateNew I rateNew).insert "rad" (.int rad)
abbrev foldStoreDaiNew (I : ExecutionEnv) (rateNew : UInt256) (rad : Int)
    (daiNew : UInt256) : Store :=
  (foldStoreRad I rateNew rad).insert "daiNew" (.int (Int.ofNat daiNew.toNat))
abbrev foldStoreDebtNew (I : ExecutionEnv)
    (rateNew : UInt256) (rad : Int) (daiNew debtNew : UInt256) : Store :=
  (foldStoreDaiNew I rateNew rad daiNew).insert "debtNew"
    (.int (Int.ofNat debtNew.toNat))
abbrev foldIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (foldIlkBytes I)
abbrev foldUsrKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (foldUsrWord I).toNat)
def foldRateSlot (I : ExecutionEnv) : UInt256 :=
  ilksBase (foldIlkKey I) + ⟨1⟩
def foldArtSlot (I : ExecutionEnv) : UInt256 :=
  ilksBase (foldIlkKey I)
def foldDaiSlot (I : ExecutionEnv) : UInt256 :=
  daiSlot (foldUsrKey I)
abbrev foldDebtSlot : UInt256 :=
  ⟨7⟩

abbrev foldPostState (evm : EVM.State) (I : ExecutionEnv)
    (rateNew daiNew debtNew : UInt256) : EVM.State :=
  Solm.EVM.storageStore
    (Solm.EVM.storageStore
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (foldRateSlot I) rateNew)
      evm.executionEnv.codeOwner (foldDaiSlot I) daiNew)
    evm.executionEnv.codeOwner foldDebtSlot debtNew

abbrev foldDaiEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "dai", steps := [.mindex (foldUsrKey I)] }

abbrev foldDebtEvaledRef : EvaledStorageRef :=
  { base := "debt", steps := [] }

theorem foldIlkBytes_length {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    (foldIlkBytes I).length = 32 := by
  unfold foldIlkBytes
  rw [List.length_take, List.length_drop]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [htlen]
  omega

theorem keyValueToWord_foldIlkKey {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    keyValueToWord (foldIlkKey I) = foldIlkWord I := by
  have hlen32 : (foldIlkBytes I).length = 32 := foldIlkBytes_length hsz100
  have hword : ABI.bytesToWord (foldIlkBytes I) = foldIlkWord I := by
    simpa [foldIlkBytes, foldIlkWord] using
      (decode_word_at_eq I.calldata 4 (by omega) (by norm_num))
  have hbytes : foldIlkBytes I = EVM.Word.toBytesBE (foldIlkWord I) := by
    have hto := toBytesBE_bytesToWord_of_length (bs := foldIlkBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  simpa [foldIlkKey, bytes32Width, hbytes] using keyValueToWord_fixedBytes32 (foldIlkWord I)

theorem foldRateSlot_eq (I : ExecutionEnv) (hsz100 : 100 ≤ I.calldata.size) :
    foldRateSlot I = solcMappingSlot ⟨2⟩ (foldIlkWord I) + ⟨1⟩ := by
  unfold foldRateSlot ilksBase foldIlkKey foldIlkWord mapSlot solcMappingSlot
  rw [keyValueToWord_foldIlkKey hsz100]
theorem foldArtSlot_eq (I : ExecutionEnv) (hsz100 : 100 ≤ I.calldata.size) :
    foldArtSlot I = solcMappingSlot ⟨2⟩ (foldIlkWord I) := by
  unfold foldArtSlot ilksBase foldIlkKey foldIlkWord mapSlot solcMappingSlot
  rw [keyValueToWord_foldIlkKey hsz100]
theorem foldDaiSlot_eq (I : ExecutionEnv) :
    foldDaiSlot I = solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I) := by
  unfold foldDaiSlot daiSlot foldUsrKey foldUsrMaskedWord mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_fold_ilksField (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (field : Ident) (hsz100 : 100 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (foldIlkValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (ilksF (.var "i") field) =
        .ok { base := "ilks", steps := [.mindex (foldIlkKey I), .field field] } := by
  have hlen : (foldIlkBytes I).length = bytes32Width.val + 1 := by
    simpa [bytes32Width] using foldIlkBytes_length (I := I) hsz100
  simp [foldIlkKey, foldIlkValue, ilksF, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind,
    bind, pure, ← Std.HashMap.get?_eq_getElem?, hi, hlen]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_fold_dai_u (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hu : locals.get? "u" = some (foldUsrValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (daiRef (.var "u")) = .ok (foldDaiEvaledRef I) := by
  simp [foldDaiEvaledRef, foldUsrValue, foldUsrKey, daiRef, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?, hu]

theorem evalStorageRef_fold_debt (evm : EVM.State) (locals : Store) :
    evalStorageRef config { contract := contract, locals := locals } evm debtRef =
      .ok foldDebtEvaledRef := by
  simp [evalStorageRef, evalStorageRefSteps, debtRef, foldDebtEvaledRef,
    EvalResult.bind, pure, bind]

theorem evalExpr_fold_ilks_rate (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz100 : 100 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (foldIlkValue I))
    (hbase : locals.get? "ilks" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "i") "rate")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (foldRateSlot I)).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := evalStorageRef_fold_ilksField evm I locals "rate" hsz100 hi)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls,
      IlkStructTy, uint256St])
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (vatStorageLocLoad_uint256 evm (foldRateSlot I))

theorem evalExpr_fold_ilks_art (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz100 : 100 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (foldIlkValue I))
    (hbase : locals.get? "ilks" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "i") "Art")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (foldArtSlot I)).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := evalStorageRef_fold_ilksField evm I locals "Art" hsz100 hi)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls,
      IlkStructTy, uint256St])
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (vatStorageLocLoad_uint256 evm (foldArtSlot I))

theorem evalExpr_fold_dai_u (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hu : locals.get? "u" = some (foldUsrValue I))
    (hbase : locals.get? "dai" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
        (.storage (daiRef (.var "u"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (foldDaiSlot I)).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := evalStorageRef_fold_dai_u evm I locals hu)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract,
      storageDecls, uint256St])
    (hloc := by
      funext evm
      change storageLayoutRaw (foldDaiEvaledRef I) evm =
        some (wordLoc (foldDaiSlot I))
      simp [storageLayoutRaw, foldDaiEvaledRef, foldDaiSlot])]
  exact congrArg EvalResult.ok (vatStorageLocLoad_uint256 evm (foldDaiSlot I))

theorem evalExpr_fold_debt (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "debt" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage debtRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner foldDebtSlot).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := evalStorageRef_fold_debt evm locals)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (vatStorageLocLoad_uint256 evm foldDebtSlot)

theorem assign_fold_rate (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (rateNew : UInt256) (hsz100 : 100 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (foldIlkValue I)) (hbase : locals.get? "ilks" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (foldRateSlot I) rateNew
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (ilksF (.var "i") "rate") (.int (Int.ofNat rateNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (ty := uint256St) (loc := wordLoc (foldRateSlot I))
    (hbase := hbase)
    (her := evalStorageRef_fold_ilksField evm I locals "rate" hsz100 hi)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls,
      IlkStructTy, uint256St])
    (hloc := by rfl)
    (hstore := by simpa [evm'] using vatStorageLocStore_uint256 evm (foldRateSlot I) rateNew)

theorem assign_fold_dai_u (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (daiNew : UInt256)
    (hu : locals.get? "u" = some (foldUsrValue I)) (hbase : locals.get? "dai" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (foldDaiSlot I) daiNew
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (daiRef (.var "u")) (.int (Int.ofNat daiNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc (foldDaiSlot I))
    (hbase := hbase)
    (her := evalStorageRef_fold_dai_u evm I locals hu)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      change storageLayoutRaw (foldDaiEvaledRef I) evm = some (wordLoc (foldDaiSlot I))
      simp [storageLayoutRaw, foldDaiEvaledRef, foldDaiSlot])
    (hstore := by simpa [evm'] using vatStorageLocStore_uint256 evm (foldDaiSlot I) daiNew)

theorem assign_fold_debt (evm : EVM.State) (locals : Store) (debtNew : UInt256)
    (hbase : locals.get? "debt" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner foldDebtSlot debtNew
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage debtRef (.int (Int.ofNat debtNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc foldDebtSlot)
    (hbase := hbase)
    (her := evalStorageRef_fold_debt evm locals)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hstore := by simpa [evm'] using vatStorageLocStore_uint256 evm foldDebtSlot debtNew)

theorem foldStore_get_i (I : ExecutionEnv) :
    (foldStore I).get? "i" = some (foldIlkValue I) := by
  unfold foldStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp
theorem foldStore_get_u (I : ExecutionEnv) :
    (foldStore I).get? "u" = some (foldUsrValue I) := by
  unfold foldStore
  rw [store_get_ne _ _ (by native_decide)]
  simp
theorem foldStore_get_rate (I : ExecutionEnv) :
    (foldStore I).get? "rate" = some (foldRateValue I) := by
  simp [foldStore]
theorem foldStoreRateNew_get_i (I : ExecutionEnv) (rateNew : UInt256) :
    (foldStoreRateNew I rateNew).get? "i" = some (foldIlkValue I) := by
  rw [foldStoreRateNew, store_get_ne _ _ (by native_decide), foldStore_get_i]
theorem foldStoreRateNew_get_u (I : ExecutionEnv) (rateNew : UInt256) :
    (foldStoreRateNew I rateNew).get? "u" = some (foldUsrValue I) := by
  rw [foldStoreRateNew, store_get_ne _ _ (by native_decide), foldStore_get_u]
theorem foldStoreRateNew_get_rate (I : ExecutionEnv) (rateNew : UInt256) :
    (foldStoreRateNew I rateNew).get? "rate" = some (foldRateValue I) := by
  rw [foldStoreRateNew, store_get_ne _ _ (by native_decide), foldStore_get_rate]
theorem foldStoreRateNew_get_rateNew (I : ExecutionEnv) (rateNew : UInt256) :
    (foldStoreRateNew I rateNew).get? "rateNew" =
      some (.int (Int.ofNat rateNew.toNat)) := by
  simp [foldStoreRateNew]
theorem foldStoreRad_get_i (I : ExecutionEnv) (rateNew : UInt256) (rad : Int) :
    (foldStoreRad I rateNew rad).get? "i" = some (foldIlkValue I) := by
  rw [foldStoreRad, store_get_ne _ _ (by native_decide),
    foldStoreRateNew_get_i]
theorem foldStoreRad_get_u (I : ExecutionEnv) (rateNew : UInt256) (rad : Int) :
    (foldStoreRad I rateNew rad).get? "u" = some (foldUsrValue I) := by
  rw [foldStoreRad, store_get_ne _ _ (by native_decide),
    foldStoreRateNew_get_u]
theorem foldStoreRad_get_rate (I : ExecutionEnv) (rateNew : UInt256) (rad : Int) :
    (foldStoreRad I rateNew rad).get? "rate" = some (foldRateValue I) := by
  rw [foldStoreRad, store_get_ne _ _ (by native_decide),
    foldStoreRateNew_get_rate]
theorem foldStoreRad_get_rad (I : ExecutionEnv) (rateNew : UInt256) (rad : Int) :
    (foldStoreRad I rateNew rad).get? "rad" = some (.int rad) := by
  simp [foldStoreRad]

theorem evalExpr_fold_mul_guard_rad_zero_art_zero_true
    (evm : EVM.State) (I : ExecutionEnv) (rateNew : UInt256)
    (hrateNe : foldRateInt I ≠ 0)
    (hart :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew 0 } evm
        (.storage (ilksF (.var "i") "Art")) = .ok (.int 0)) :
    evalExpr? config { contract := contract, locals := foldStoreRad I rateNew 0 } evm
      (eitherExpr (.binary .eq (.var "rate") (.intLit 0))
        (.binary .eq (.binary .div (.var "rad") (.var "rate"))
          (.storage (ilksF (.var "i") "Art")))) =
      .ok (.bool true) := by
  have hrate :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew 0 } evm
        (.var "rate") = .ok (.int (foldRateInt I)) :=
    vatEvalExpr_varInt (foldStoreRad_get_rate I rateNew 0)
  have hrad :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew 0 } evm
        (.var "rad") = .ok (.int 0) :=
    vatEvalExpr_varInt (foldStoreRad_get_rad I rateNew 0)
  have hleft :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew 0 } evm
        (.binary .eq (.var "rate") (.intLit 0)) = .ok (.bool false) := by
    simp [evalExpr?, EvalResult.bind, bind, hrate, evalBinaryOp?, hrateNe]
  have hright :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew 0 } evm
        (.binary .eq (.binary .div (.var "rad") (.var "rate"))
          (.storage (ilksF (.var "i") "Art"))) =
      .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind, hrad, hrate, hart, evalBinaryOp?, hrateNe]
  exact vatEvalExpr_or_false_right hleft hright

theorem evalExpr_fold_mul_guard_rate_zero_true
    (evm : EVM.State) (I : ExecutionEnv) (rateNew : UInt256) (rad : Int)
    (hrateZero : foldRateInt I = 0) :
    evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
      (eitherExpr (.binary .eq (.var "rate") (.intLit 0))
        (.binary .eq (.binary .div (.var "rad") (.var "rate"))
          (.storage (ilksF (.var "i") "Art")))) =
      .ok (.bool true) := by
  have hrate0 :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (.var "rate") = .ok (.int 0) := by
    simpa [hrateZero] using
      vatEvalExpr_varInt (foldStoreRad_get_rate I rateNew rad)
  have heq0 :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (.binary .eq (.var "rate") (.intLit 0)) = .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind, hrate0, evalBinaryOp?]
  exact vatEvalExpr_or_true_left heq0

theorem evalExpr_fold_mul_guard_exact_true
    (evm : EVM.State) (I : ExecutionEnv) (rateNew : UInt256) (rad : Int)
    {art : Int}
    (hrateNe : foldRateInt I ≠ 0)
    (hdiv : rad / foldRateInt I = art)
    (hart :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (.storage (ilksF (.var "i") "Art")) = .ok (.int art)) :
    evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
      (eitherExpr (.binary .eq (.var "rate") (.intLit 0))
        (.binary .eq (.binary .div (.var "rad") (.var "rate"))
          (.storage (ilksF (.var "i") "Art")))) =
      .ok (.bool true) := by
  have hrate :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (.var "rate") = .ok (.int (foldRateInt I)) :=
    vatEvalExpr_varInt (foldStoreRad_get_rate I rateNew rad)
  have hrad :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (.var "rad") = .ok (.int rad) :=
    vatEvalExpr_varInt (foldStoreRad_get_rad I rateNew rad)
  have hleft :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (.binary .eq (.var "rate") (.intLit 0)) = .ok (.bool false) := by
    simp [evalExpr?, EvalResult.bind, bind, hrate, evalBinaryOp?, hrateNe]
  have hright :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (.binary .eq (.binary .div (.var "rad") (.var "rate"))
          (.storage (ilksF (.var "i") "Art"))) =
      .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind, hrad, hrate, hart, evalBinaryOp?,
      hrateNe, hdiv]
  exact vatEvalExpr_or_false_right hleft hright

theorem evalExpr_fold_mul_guard_false
    (evm : EVM.State) (I : ExecutionEnv) (rateNew : UInt256) (rad : Int)
    {art : Int}
    (hrateNe : foldRateInt I ≠ 0)
    (hdivNe : rad / foldRateInt I ≠ art)
    (hart :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (.storage (ilksF (.var "i") "Art")) = .ok (.int art)) :
    evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
      (eitherExpr (.binary .eq (.var "rate") (.intLit 0))
        (.binary .eq (.binary .div (.var "rad") (.var "rate"))
          (.storage (ilksF (.var "i") "Art")))) =
      .ok (.bool false) := by
  have hrate :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (.var "rate") = .ok (.int (foldRateInt I)) :=
    vatEvalExpr_varInt (foldStoreRad_get_rate I rateNew rad)
  have hrad :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (.var "rad") = .ok (.int rad) :=
    vatEvalExpr_varInt (foldStoreRad_get_rad I rateNew rad)
  have hleft :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (.binary .eq (.var "rate") (.intLit 0)) = .ok (.bool false) := by
    simp [evalExpr?, EvalResult.bind, bind, hrate, evalBinaryOp?, hrateNe]
  have hright :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (.binary .eq (.binary .div (.var "rad") (.var "rate"))
          (.storage (ilksF (.var "i") "Art"))) =
      .ok (.bool false) := by
    simp [evalExpr?, EvalResult.bind, bind, hrad, hrate, hart, evalBinaryOp?,
      hrateNe, hdivNe]
  exact vatEvalExpr_or_false_right hleft hright

theorem fold_rad_mod_word (I : ExecutionEnv) (art : UInt256) :
    (Int.ofNat art.toNat * foldRateInt I) % (Int.ofNat EVM.wordModulus) =
      Int.ofNat (UInt256.mul (foldRateWord I) art).toNat := by
  have hartLt : art.toNat < EVM.wordModulus := by
    change art.val.val < EVM.twoPow 256
    exact art.val.isLt
  calc
    (Int.ofNat art.toNat * foldRateInt I) % (Int.ofNat EVM.wordModulus)
        = (Int.ofNat art.toNat % Int.ofNat EVM.wordModulus *
            (foldRateInt I % Int.ofNat EVM.wordModulus)) %
            Int.ofNat EVM.wordModulus := by
          rw [Int.mul_emod]
    _ = (Int.ofNat art.toNat * Int.ofNat (foldRateWord I).toNat) %
            Int.ofNat EVM.wordModulus := by
          rw [foldRateInt_mod_word]
          have hartMod :
              Int.ofNat art.toNat % Int.ofNat EVM.wordModulus =
                Int.ofNat art.toNat :=
            Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hartLt)
          rw [hartMod]
    _ = Int.ofNat ((art.toNat * (foldRateWord I).toNat) % EVM.wordModulus) := by
          change Int.ofNat (art.toNat * (foldRateWord I).toNat) %
              Int.ofNat EVM.wordModulus =
            Int.ofNat ((art.toNat * (foldRateWord I).toNat) % EVM.wordModulus)
          exact (Int.natCast_emod (art.toNat * (foldRateWord I).toNat)
            EVM.wordModulus).symm
    _ = Int.ofNat (UInt256.mul (foldRateWord I) art).toNat := by
          rw [u256_mul_toNat]
          rw [Nat.mul_comm art.toNat (foldRateWord I).toNat]
          rw [show EVM.wordModulus = UInt256.size by rfl]

theorem vatFoldSourceRevertAfterDaiBlock (evm evmRate : EVM.State) (I : ExecutionEnv)
    {rateNew : UInt256} {rad : Int}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      evalExpr? config { contract := contract, locals := foldStore I } evm
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true))
    (hlive :
      evalExpr? config { contract := contract, locals := foldStore I } evm
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true))
    (hrateOk :
      ExecBlock config { contract := contract, locals := foldStore I } evm
        (checkedAddSignedInto "rateNew" (.storage (ilksF (.var "i") "rate")) (.var "rate") ++
          [ .assign .storage (ilksF (.var "i") "rate") (.var "rateNew") ])
        (.ok { contract := contract, locals := foldStoreRateNew I rateNew } evmRate))
    (hradOk :
      ExecBlock config { contract := contract, locals := foldStoreRateNew I rateNew } evmRate
        (checkedMulSignedInto "rad" (.storage (ilksF (.var "i") "Art")) (.var "rate"))
        (.ok { contract := contract, locals := foldStoreRad I rateNew rad } evmRate))
    (hdaiRevert :
      ExecBlock config { contract := contract, locals := foldStoreRad I rateNew rad } evmRate
        (checkedAddSignedInto "daiNew" (.storage (daiRef (.var "u"))) (.var "rad"))
        .reverted) :
    ExecTransitionBody config contract evm (foldStore I) foldTransition.body .reverted := by
  have hprefix :
      ExecBlock config { contract := contract, locals := foldStore I } evm
        (nonpayable ++ auth ++ requireLive)
        (.ok { contract := contract, locals := foldStore I } evm) := by
    change ExecBlock config { contract := contract, locals := foldStore I } evm
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
        .require (.binary .eq (.storage liveRef) (.intLit 1)) ]
      (.ok { contract := contract, locals := foldStore I } evm)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true hwv
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauth) ?_
    exact ExecBlock.consNormal (ExecStmt.requireTrue hlive) ExecBlock.nil
  have h01 := execBlock_append hprefix hrateOk
  have h02 := execBlock_append h01 hradOk
  have h03 := execBlock_append h02 hdaiRevert
  have hblock := execBlock_append_term
    (s2 :=
      [ .assign .storage (daiRef (.var "u")) (.var "daiNew") ] ++
      checkedAddSignedInto "debtNew" (.storage debtRef) (.var "rad") ++
      [ .assign .storage debtRef (.var "debtNew") ])
    h03 (by intro f e h; cases h)
  simpa [ExecTransitionBody, foldTransition, nonpayable, auth, requireLive,
    List.append_assoc] using ExecFuncBody.execBlockRevert hblock

theorem vatFoldSourceRevertAfterDebtBlock
    (evm evmRate evmDai : EVM.State) (I : ExecutionEnv)
    {rateNew daiNew : UInt256} {rad : Int}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      evalExpr? config { contract := contract, locals := foldStore I } evm
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true))
    (hlive :
      evalExpr? config { contract := contract, locals := foldStore I } evm
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true))
    (hrateOk :
      ExecBlock config { contract := contract, locals := foldStore I } evm
        (checkedAddSignedInto "rateNew" (.storage (ilksF (.var "i") "rate")) (.var "rate") ++
          [ .assign .storage (ilksF (.var "i") "rate") (.var "rateNew") ])
        (.ok { contract := contract, locals := foldStoreRateNew I rateNew } evmRate))
    (hradOk :
      ExecBlock config { contract := contract, locals := foldStoreRateNew I rateNew } evmRate
        (checkedMulSignedInto "rad" (.storage (ilksF (.var "i") "Art")) (.var "rate"))
        (.ok { contract := contract, locals := foldStoreRad I rateNew rad } evmRate))
    (hdaiOk :
      ExecBlock config { contract := contract, locals := foldStoreRad I rateNew rad } evmRate
        (checkedAddSignedInto "daiNew" (.storage (daiRef (.var "u"))) (.var "rad"))
        (.ok { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew } evmRate))
    (hdaiAssign :
      ExecBlock config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew }
        evmRate [ .assign .storage (daiRef (.var "u")) (.var "daiNew") ]
        (.ok { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew } evmDai))
    (hdebtRevert :
      ExecBlock config { contract := contract, locals := foldStoreDaiNew I rateNew rad daiNew }
        evmDai (checkedAddSignedInto "debtNew" (.storage debtRef) (.var "rad"))
        .reverted) :
    ExecTransitionBody config contract evm (foldStore I) foldTransition.body .reverted := by
  have hprefix :
      ExecBlock config { contract := contract, locals := foldStore I } evm
        (nonpayable ++ auth ++ requireLive)
        (.ok { contract := contract, locals := foldStore I } evm) := by
    change ExecBlock config { contract := contract, locals := foldStore I } evm
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
        .require (.binary .eq (.storage liveRef) (.intLit 1)) ]
      (.ok { contract := contract, locals := foldStore I } evm)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true hwv
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauth) ?_
    exact ExecBlock.consNormal (ExecStmt.requireTrue hlive) ExecBlock.nil
  have h01 := execBlock_append hprefix hrateOk
  have h02 := execBlock_append h01 hradOk
  have h03 := execBlock_append h02 hdaiOk
  have h04 := execBlock_append h03 hdaiAssign
  have h05 := execBlock_append h04 hdebtRevert
  have hblock := execBlock_append_term
    (s2 := [ .assign .storage debtRef (.var "debtNew") ])
    h05 (by intro f e h; cases h)
  simpa [ExecTransitionBody, foldTransition, nonpayable, auth, requireLive,
    List.append_assoc] using ExecFuncBody.execBlockRevert hblock

theorem foldStore_ilks (I : ExecutionEnv) :
    (foldStore I).get? "ilks" = none := by
  unfold foldStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp
theorem foldStoreRateNew_ilks (I : ExecutionEnv) (rateNew : UInt256) :
    (foldStoreRateNew I rateNew).get? "ilks" = none := by
  rw [foldStoreRateNew, store_get_ne _ _ (by native_decide), foldStore_ilks]
theorem foldStoreRad_ilks (I : ExecutionEnv) (rateNew : UInt256) (rad : Int) :
    (foldStoreRad I rateNew rad).get? "ilks" = none := by
  rw [foldStoreRad, store_get_ne _ _ (by native_decide), foldStoreRateNew_ilks]

theorem vatFoldRadMulRevertGuardFalse (evm : EVM.State) (I : ExecutionEnv)
    {rateNew artOld : UInt256} {rad : Int} (hsz100 : 100 ≤ I.calldata.size)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (foldArtSlot I) = artOld)
    (hrad : rad = Int.ofNat artOld.toNat * foldRateInt I)
    (hradLo : -((2 : Int) ^ 255) ≤ rad)
    (hradHi : rad < (2 : Int) ^ 255)
    (hguardMax :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (.binary .le (.storage (ilksF (.var "i") "Art")) (.intLit maxInt256)) =
        .ok (.bool true))
    (hguardMul :
      evalExpr? config { contract := contract, locals := foldStoreRad I rateNew rad } evm
        (eitherExpr (.binary .eq (.var "rate") (.intLit 0))
          (.binary .eq (.binary .div (.var "rad") (.var "rate"))
            (.storage (ilksF (.var "i") "Art")))) =
        .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := foldStoreRateNew I rateNew } evm
      (checkedMulSignedInto "rad" (.storage (ilksF (.var "i") "Art")) (.var "rate"))
      .reverted := by
  have hart :
      evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNew } evm
          (.storage (ilksF (.var "i") "Art")) =
        .ok (.int (Int.ofNat artOld.toNat)) := by
    rw [evalExpr_fold_ilks_art evm I (foldStoreRateNew I rateNew) hsz100
      (foldStoreRateNew_get_i I rateNew) (foldStoreRateNew_ilks I rateNew)]
    rw [hload]
  have hrate :
      evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNew } evm
        (.var "rate") = .ok (.int (foldRateInt I)) :=
    vatEvalExpr_varInt (foldStoreRateNew_get_rate I rateNew)
  have hmul :
      evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNew } evm
        (.binary .mul (.storage (ilksF (.var "i") "Art")) (.var "rate")) =
        .ok (.int rad) :=
    evalExpr_fold_mul_int_ok hart hrate hrad
  have hlet :
      evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNew } evm
        (s256 (.binary .mul (.storage (ilksF (.var "i") "Art")) (.var "rate"))) =
        .ok (.int rad) :=
    evalExpr_fold_s256_ok hmul hradLo hradHi
  change ExecBlock config { contract := contract, locals := foldStoreRateNew I rateNew } evm
    [ .letDecl "rad" (some int256)
        (s256 (.binary .mul (.storage (ilksF (.var "i") "Art")) (.var "rate"))),
      .require (.binary .le (.storage (ilksF (.var "i") "Art")) (.intLit maxInt256)),
      .require
        (eitherExpr (.binary .eq (.var "rate") (.intLit 0))
          (.binary .eq (.binary .div (.var "rad") (.var "rate"))
            (.storage (ilksF (.var "i") "Art")))) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardMax) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguardMul)

theorem vatFoldRadMulRevertRange (evm : EVM.State) (I : ExecutionEnv)
    {rateNew artOld : UInt256} (hsz100 : 100 ≤ I.calldata.size)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (foldArtSlot I) = artOld)
    (hbad :
      Int.ofNat artOld.toNat * foldRateInt I < -((2 : Int) ^ 255) ∨
        Int.ofNat artOld.toNat * foldRateInt I ≥ (2 : Int) ^ 255) :
    ExecBlock config { contract := contract, locals := foldStoreRateNew I rateNew } evm
      (checkedMulSignedInto "rad" (.storage (ilksF (.var "i") "Art")) (.var "rate"))
      .reverted := by
  let prod := Int.ofNat artOld.toNat * foldRateInt I
  have hart :
      evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNew } evm
          (.storage (ilksF (.var "i") "Art")) =
        .ok (.int (Int.ofNat artOld.toNat)) := by
    rw [evalExpr_fold_ilks_art evm I (foldStoreRateNew I rateNew) hsz100
      (foldStoreRateNew_get_i I rateNew) (foldStoreRateNew_ilks I rateNew)]
    rw [hload]
  have hrate :
      evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNew } evm
        (.var "rate") = .ok (.int (foldRateInt I)) :=
    vatEvalExpr_varInt (foldStoreRateNew_get_rate I rateNew)
  have hmul :
      evalExpr? config { contract := contract, locals := foldStoreRateNew I rateNew } evm
        (.binary .mul (.storage (ilksF (.var "i") "Art")) (.var "rate")) =
        .ok (.int prod) :=
    evalExpr_fold_mul_int_ok hart hrate rfl
  change ExecBlock config { contract := contract, locals := foldStoreRateNew I rateNew } evm
    [ .letDecl "rad" (some int256)
        (s256 (.binary .mul (.storage (ilksF (.var "i") "Art")) (.var "rate"))),
      .require (.binary .le (.storage (ilksF (.var "i") "Art")) (.intLit maxInt256)),
      .require
        (eitherExpr (.binary .eq (.var "rate") (.intLit 0))
          (.binary .eq (.binary .div (.var "rad") (.var "rate"))
            (.storage (ilksF (.var "i") "Art")))) ]
    .reverted
  have hbadProd : prod < -((2 : Int) ^ 255) ∨ prod ≥ (2 : Int) ^ 255 := by
    exact hbad
  exact ExecBlock.consRevert
    (ExecStmt.letDeclRevert (evalExpr_s256_revert hmul hbadProd))

theorem foldStoreDaiNew_get_u (I : ExecutionEnv) (rateNew : UInt256) (rad : Int)
    (daiNew : UInt256) :
    (foldStoreDaiNew I rateNew rad daiNew).get? "u" = some (foldUsrValue I) := by
  rw [foldStoreDaiNew, store_get_ne _ _ (by native_decide),
    foldStoreRad_get_u]
theorem foldStoreDaiNew_get_rad (I : ExecutionEnv) (rateNew : UInt256) (rad : Int)
    (daiNew : UInt256) :
    (foldStoreDaiNew I rateNew rad daiNew).get? "rad" = some (.int rad) := by
  rw [foldStoreDaiNew, store_get_ne _ _ (by native_decide),
    foldStoreRad_get_rad]
theorem foldStoreDaiNew_get_daiNew (I : ExecutionEnv) (rateNew : UInt256)
    (rad : Int) (daiNew : UInt256) :
    (foldStoreDaiNew I rateNew rad daiNew).get? "daiNew" =
      some (.int (Int.ofNat daiNew.toNat)) := by
  simp [foldStoreDaiNew]
theorem foldStoreDebtNew_get_daiNew (I : ExecutionEnv)
    (rateNew : UInt256) (rad : Int) (daiNew debtNew : UInt256) :
    (foldStoreDebtNew I rateNew rad daiNew debtNew).get? "daiNew" =
      some (.int (Int.ofNat daiNew.toNat)) := by
  rw [foldStoreDebtNew, store_get_ne _ _ (by native_decide),
    foldStoreDaiNew_get_daiNew]
theorem foldStoreDebtNew_get_rad (I : ExecutionEnv)
    (rateNew : UInt256) (rad : Int) (daiNew debtNew : UInt256) :
    (foldStoreDebtNew I rateNew rad daiNew debtNew).get? "rad" = some (.int rad) := by
  rw [foldStoreDebtNew, store_get_ne _ _ (by native_decide),
    foldStoreDaiNew_get_rad]
theorem foldStoreDebtNew_get_debtNew (I : ExecutionEnv)
    (rateNew : UInt256) (rad : Int) (daiNew debtNew : UInt256) :
    (foldStoreDebtNew I rateNew rad daiNew debtNew).get? "debtNew" =
      some (.int (Int.ofNat debtNew.toNat)) := by
  simp [foldStoreDebtNew]

theorem RD.vatFoldDaiStoreOk
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray} {rad base : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5782⟩
      [rad, ⟨0⟩, base, foldRateWord I, foldUsrMaskedWord I, foldIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hneg :
      UInt256.slt rad ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (rad + solcSlotWord σ I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I)))
          (solcSlotWord σ I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I))) = ⟨0⟩)
    (hpos :
      UInt256.sgt rad ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (rad + solcSlotWord σ I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I)))
          (solcSlotWord σ I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I))) = ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5846⟩
      [rad, base, foldRateWord I, foldUsrMaskedWord I, foldIlkWord I, ⟨524⟩, sel]
      (twoWordHashMem (foldUsrMaskedWord I) ⟨5⟩
        (twoWordHashMem (foldUsrMaskedWord I) ⟨5⟩ mem))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ
        (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I))
        (rad + solcSlotWord σ I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I)))) k' C' := by
  let daiSlotWord := solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I)
  let old := solcSlotWord σ I daiSlotWord
  let sum := rad + old
  have rd5783 := h.jumpdest (by native_decide) (by evm_ov)
  have rd5785 := rd5783.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd5787 := rd5785.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd5789 := rd5787.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd5790 := rd5789.shl (by native_decide) (by evm_ov)
  have rd5791 := rd5790.sub (by native_decide) (by evm_ov)
  have rd5792pre := rd5791.dup6 (by native_decide) (by evm_ov)
  have rd5793pre := rd5792pre.and (by native_decide) (by evm_ov)
  have hmask :
      UInt256.land (foldUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        foldUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact foldUsrMaskedWord_clean I
  have rd5793 := rd5793pre
  rw [hmask] at rd5793
  have rd5795 := rd5793.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd5796 := rd5795.swap1 (by native_decide) (by evm_ov)
  have rd5797 := rd5796.dup2 (by native_decide) (by evm_ov)
  have rd5798 := rd5797.mstore 0 (wordAt0Mem (foldUsrMaskedWord I) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd5800 := rd5798.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  have rd5802 := rd5800.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd5803 := rd5802.mstore 0 (twoWordHashMem (foldUsrMaskedWord I) ⟨5⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd5805 := rd5803.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd5806 := rd5805.swap1 (by native_decide) (by evm_ov)
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (foldUsrMaskedWord I) ⟨5⟩ mem).readWithPadding 0 64))) =
        daiSlotWord := by
    simpa [daiSlotWord] using
      twoWordHashMem_solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I) hmem
  have rd5807pre := rd5806.keccak256 0 daiSlotWord (UInt256.ofNat 3)
    (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5808raw⟩ := rd5807pre.sload (by native_decide) (by evm_ov)
  have hold :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD daiSlotWord ⟨0⟩)) = old := by
    simp [old, solcSlotWord]
  have rd5808 := rd5808raw
  rw [hold] at rd5808
  have rd5809 := rd5808.swap1 (by native_decide) (by evm_ov)
  have rd5810 := rd5809.swap2 (by native_decide) (by evm_ov)
  have rd5811 := rd5810.pop (by native_decide) (by evm_ov)
  have rd5814 := rd5811.push2 ⟨5820⟩ (by native_decide) (by evm_ov)
  have rd5815 := rd5814.swap1 (by native_decide) (by evm_ov)
  have rd5816 := rd5815.dup3 (by native_decide) (by evm_ov)
  have rd5819 := rd5816.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd5819.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd5820⟩ := RD.vatSignedAddOk
    (x := old) (y := rad) (ret := ⟨5820⟩)
    (R := [rad, base, foldRateWord I, foldUsrMaskedWord I, foldIlkWord I, ⟨524⟩, sel])
    rd6653 (by simpa [old, daiSlotWord] using hneg)
    (by simpa [old, daiSlotWord] using hpos)
    (by jump_dest) (by simp)
  have rd5821 := rd5820.jumpdest (by native_decide) (by evm_ov)
  have rd5823 := rd5821.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd5825 := rd5823.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd5827 := rd5825.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd5828 := rd5827.shl (by native_decide) (by evm_ov)
  have rd5829 := rd5828.sub (by native_decide) (by evm_ov)
  have rd5830pre := rd5829.dup6 (by native_decide) (by evm_ov)
  have rd5831pre := rd5830pre.and (by native_decide) (by evm_ov)
  have rd5831 := rd5831pre
  rw [hmask] at rd5831
  have rd5833 := rd5831.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd5834 := rd5833.swap1 (by native_decide) (by evm_ov)
  have rd5835 := rd5834.dup2 (by native_decide) (by evm_ov)
  have rd5836 := rd5835.mstore 0 (wordAt0Mem (foldUsrMaskedWord I)
    (twoWordHashMem (foldUsrMaskedWord I) ⟨5⟩ mem)) (UInt256.ofNat 3)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd5838 := rd5836.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  have rd5840 := rd5838.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd5841 := rd5840.mstore 0
    (twoWordHashMem (foldUsrMaskedWord I) ⟨5⟩
      (twoWordHashMem (foldUsrMaskedWord I) ⟨5⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd5843 := rd5841.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd5844 := rd5843.swap1 (by native_decide) (by evm_ov)
  have hmemDai :
      (twoWordHashMem (foldUsrMaskedWord I) ⟨5⟩ mem).size = 96 :=
    twoWordHashMem_size_96 (foldUsrMaskedWord I) ⟨5⟩ hmem
  have hslot2 :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC
            ((twoWordHashMem (foldUsrMaskedWord I) ⟨5⟩
              (twoWordHashMem (foldUsrMaskedWord I) ⟨5⟩ mem)).readWithPadding 0 64))) =
        daiSlotWord := by
    simpa [daiSlotWord] using
      twoWordHashMem_solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I) hmemDai
  have rd5845pre := rd5844.keccak256 0 daiSlotWord (UInt256.ofNat 3)
    (by native_decide) mem_cost hslot2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5846⟩ := rd5845pre.sstore hperm (by native_decide) (by norm_num)
  exact ⟨_, _, by simpa [daiSlotWord, old, sum] using rd5846⟩

theorem RD.vatFoldDaiStoreRevert
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray} {rad base : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5782⟩
      [rad, ⟨0⟩, base, foldRateWord I, foldUsrMaskedWord I, foldIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hfail :
      ¬ (UInt256.slt rad ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (rad + solcSlotWord σ I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I)))
          (solcSlotWord σ I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I))) = ⟨0⟩) ∨
      (UInt256.slt rad ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (rad + solcSlotWord σ I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I)))
          (solcSlotWord σ I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I))) = ⟨0⟩) ∧
        ¬ (UInt256.sgt rad ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (rad + solcSlotWord σ I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I)))
            (solcSlotWord σ I (solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I))) = ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  let daiSlotWord := solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I)
  let old := solcSlotWord σ I daiSlotWord
  let sum := rad + old
  have rd5783 := h.jumpdest (by native_decide) (by evm_ov)
  have rd5785 := rd5783.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd5787 := rd5785.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd5789 := rd5787.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd5790 := rd5789.shl (by native_decide) (by evm_ov)
  have rd5791 := rd5790.sub (by native_decide) (by evm_ov)
  have rd5792pre := rd5791.dup6 (by native_decide) (by evm_ov)
  have rd5793pre := rd5792pre.and (by native_decide) (by evm_ov)
  have hmask :
      UInt256.land (foldUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        foldUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact foldUsrMaskedWord_clean I
  have rd5793 := rd5793pre
  rw [hmask] at rd5793
  have rd5795 := rd5793.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd5796 := rd5795.swap1 (by native_decide) (by evm_ov)
  have rd5797 := rd5796.dup2 (by native_decide) (by evm_ov)
  have rd5798 := rd5797.mstore 0 (wordAt0Mem (foldUsrMaskedWord I) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd5800 := rd5798.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  have rd5802 := rd5800.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd5803 := rd5802.mstore 0 (twoWordHashMem (foldUsrMaskedWord I) ⟨5⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd5805 := rd5803.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd5806 := rd5805.swap1 (by native_decide) (by evm_ov)
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (foldUsrMaskedWord I) ⟨5⟩ mem).readWithPadding 0 64))) =
        daiSlotWord := by
    simpa [daiSlotWord] using
      twoWordHashMem_solcMappingSlot ⟨5⟩ (foldUsrMaskedWord I) hmem
  have rd5807pre := rd5806.keccak256 0 daiSlotWord (UInt256.ofNat 3)
    (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5808raw⟩ := rd5807pre.sload (by native_decide) (by evm_ov)
  have hold :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD daiSlotWord ⟨0⟩)) = old := by
    simp [old, solcSlotWord]
  have rd5808 := rd5808raw
  rw [hold] at rd5808
  have rd5809 := rd5808.swap1 (by native_decide) (by evm_ov)
  have rd5810 := rd5809.swap2 (by native_decide) (by evm_ov)
  have rd5811 := rd5810.pop (by native_decide) (by evm_ov)
  have rd5814 := rd5811.push2 ⟨5820⟩ (by native_decide) (by evm_ov)
  have rd5815 := rd5814.swap1 (by native_decide) (by evm_ov)
  have rd5816 := rd5815.dup3 (by native_decide) (by evm_ov)
  have rd5819 := rd5816.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd5819.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatSignedAddRevert
    (x := old) (y := rad) (ret := ⟨5820⟩)
    (R := [rad, base, foldRateWord I, foldUsrMaskedWord I, foldIlkWord I, ⟨524⟩, sel])
    rd6653 (by simpa [old, daiSlotWord, sum] using hfail) (by simp)

theorem RD.vatFoldDebtStoreReturnOk
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray} {rad base : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5846⟩
      [rad, base, foldRateWord I, foldUsrMaskedWord I, foldIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hneg :
      UInt256.slt rad ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (rad + solcSlotWord σ I ⟨7⟩)
          (solcSlotWord σ I ⟨7⟩) = ⟨0⟩)
    (hpos :
      UInt256.sgt rad ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (rad + solcSlotWord σ I ⟨7⟩)
          (solcSlotWord σ I ⟨7⟩) = ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨524⟩ [sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨7⟩
        (rad + solcSlotWord σ I ⟨7⟩)) k' C' := by
  let old := solcSlotWord σ I ⟨7⟩
  let sum := rad + old
  have rd5848 := h.push1 ⟨7⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5849raw⟩ := rd5848.sload (by native_decide) (by evm_ov)
  have hold :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨7⟩ ⟨0⟩)) =
        old := by
    simp [old, solcSlotWord]
  have rd5849 := rd5849raw
  rw [hold] at rd5849
  have rd5852 := rd5849.push2 ⟨5858⟩ (by native_decide) (by evm_ov)
  have rd5853 := rd5852.swap1 (by native_decide) (by evm_ov)
  have rd5854 := rd5853.dup3 (by native_decide) (by evm_ov)
  have rd5857 := rd5854.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd5857.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd5858⟩ := RD.vatSignedAddOk
    (x := old) (y := rad) (ret := ⟨5858⟩)
    (R := [rad, base, foldRateWord I, foldUsrMaskedWord I, foldIlkWord I, ⟨524⟩, sel])
    rd6653 (by simpa [old] using hneg)
    (by simpa [old] using hpos)
    (by jump_dest) (by simp)
  have rd5859 := rd5858.jumpdest (by native_decide) (by evm_ov)
  have rd5861pre := rd5859.push1 ⟨7⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5862⟩ := rd5861pre.sstore hperm (by native_decide) (by norm_num)
  have rd5863 := rd5862.pop (by native_decide) (by evm_ov)
  have rd5864 := rd5863.pop (by native_decide) (by evm_ov)
  have rd5865 := rd5864.pop (by native_decide) (by evm_ov)
  have rd5866 := rd5865.pop (by native_decide) (by evm_ov)
  have rd5867 := rd5866.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [old, sum] using rd5867.jump (by native_decide) (by jump_dest)
      (by evm_ov)⟩

theorem RD.vatFoldDebtStoreRevert
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray} {rad base : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5846⟩
      [rad, base, foldRateWord I, foldUsrMaskedWord I, foldIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hfail :
      ¬ (UInt256.slt rad ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (rad + solcSlotWord σ I ⟨7⟩) (solcSlotWord σ I ⟨7⟩) = ⟨0⟩) ∨
      (UInt256.slt rad ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (rad + solcSlotWord σ I ⟨7⟩) (solcSlotWord σ I ⟨7⟩) = ⟨0⟩) ∧
        ¬ (UInt256.sgt rad ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt (rad + solcSlotWord σ I ⟨7⟩) (solcSlotWord σ I ⟨7⟩) = ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  let old := solcSlotWord σ I ⟨7⟩
  let sum := rad + old
  have rd5848 := h.push1 ⟨7⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5849raw⟩ := rd5848.sload (by native_decide) (by evm_ov)
  have hold :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨7⟩ ⟨0⟩)) =
        old := by
    simp [old, solcSlotWord]
  have rd5849 := rd5849raw
  rw [hold] at rd5849
  have rd5852 := rd5849.push2 ⟨5858⟩ (by native_decide) (by evm_ov)
  have rd5853 := rd5852.swap1 (by native_decide) (by evm_ov)
  have rd5854 := rd5853.dup3 (by native_decide) (by evm_ov)
  have rd5857 := rd5854.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd5857.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatSignedAddRevert
    (x := old) (y := rad) (ret := ⟨5858⟩)
    (R := [rad, base, foldRateWord I, foldUsrMaskedWord I, foldIlkWord I, ⟨524⟩, sel])
    rd6653 (by simpa [old, sum] using hfail) (by simp)

theorem foldStore_dai (I : ExecutionEnv) :
    (foldStore I).get? "dai" = none := by
  unfold foldStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp
theorem foldStoreRad_dai (I : ExecutionEnv) (rateNew : UInt256) (rad : Int) :
    (foldStoreRad I rateNew rad).get? "dai" = none := by
  rw [foldStoreRad, store_get_ne _ _ (by native_decide)]
  rw [foldStoreRateNew, store_get_ne _ _ (by native_decide), foldStore_dai]
theorem foldStoreDaiNew_dai (I : ExecutionEnv) (rateNew : UInt256) (rad : Int)
    (daiNew : UInt256) :
    (foldStoreDaiNew I rateNew rad daiNew).get? "dai" = none := by
  rw [foldStoreDaiNew, store_get_ne _ _ (by native_decide), foldStoreRad_dai]
theorem foldStore_debt (I : ExecutionEnv) :
    (foldStore I).get? "debt" = none := by
  unfold foldStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp
theorem foldStoreDaiNew_debt (I : ExecutionEnv) (rateNew : UInt256) (rad : Int)
    (daiNew : UInt256) :
    (foldStoreDaiNew I rateNew rad daiNew).get? "debt" = none := by
  rw [foldStoreDaiNew, store_get_ne _ _ (by native_decide)]
  rw [foldStoreRad, store_get_ne _ _ (by native_decide)]
  rw [foldStoreRateNew, store_get_ne _ _ (by native_decide), foldStore_debt]
theorem foldStoreDebtNew_debt (I : ExecutionEnv)
    (rateNew : UInt256) (rad : Int) (daiNew debtNew : UInt256) :
    (foldStoreDebtNew I rateNew rad daiNew debtNew).get? "debt" = none := by
  rw [foldStoreDebtNew, store_get_ne _ _ (by native_decide), foldStoreDaiNew_debt]
theorem foldStore_wards (I : ExecutionEnv) :
    (foldStore I).get? "wards" = none := by
  unfold foldStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp
theorem foldStore_live (I : ExecutionEnv) :
    (foldStore I).get? "live" = none := by
  unfold foldStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

end Benchmarks.Dss.Vat

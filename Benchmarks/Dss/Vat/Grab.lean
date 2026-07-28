import Benchmarks.Dss.Vat.Common
import Benchmarks.Dss.Vat.Signed
import Benchmarks.Dss.Vat.FoldCommon

namespace Benchmarks.Dss.Vat

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

/-! ## `grab(bytes32,address,address,address,int256,int256)` -/

abbrev grabIWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev grabUWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev grabVWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev grabWWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 100

abbrev grabUMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (grabUWord I)

abbrev grabVMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (grabVWord I)

abbrev grabWMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (grabWWord I)

abbrev grabDinkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 132

abbrev grabDartWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 164

abbrev grabDinkInt (I : ExecutionEnv) : Int :=
  if (grabDinkWord I).toNat < EVM.twoPow 255 then
    Int.ofNat (grabDinkWord I).toNat
  else
    Int.ofNat (grabDinkWord I).toNat - Int.ofNat EVM.wordModulus

abbrev grabDartInt (I : ExecutionEnv) : Int :=
  if (grabDartWord I).toNat < EVM.twoPow 255 then
    Int.ofNat (grabDartWord I).toNat
  else
    Int.ofNat (grabDartWord I).toNat - Int.ofNat EVM.wordModulus

theorem grabDinkInt_mod_word (I : ExecutionEnv) :
    grabDinkInt I % (Int.ofNat EVM.wordModulus) =
      Int.ofNat (grabDinkWord I).toNat := by
  have hltMod :
      Int.ofNat (grabDinkWord I).toNat < Int.ofNat EVM.wordModulus := by
    exact Int.ofNat_lt.mpr (by
      change (grabDinkWord I).val.val < EVM.twoPow 256
      exact (grabDinkWord I).val.isLt)
  have hbase :
      Int.ofNat (grabDinkWord I).toNat % Int.ofNat EVM.wordModulus =
        Int.ofNat (grabDinkWord I).toNat :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) hltMod
  unfold grabDinkInt
  split
  · exact hbase
  · rw [← Int.emod_eq_sub_self_emod]
    exact hbase

theorem grabDinkInt_lo (I : ExecutionEnv) :
    -((2 : Int) ^ 255) ≤ grabDinkInt I := by
  unfold grabDinkInt
  by_cases h : (grabDinkWord I).toNat < EVM.twoPow 255
  · rw [if_pos h]
    have hnonneg : (0 : Int) ≤ Int.ofNat (grabDinkWord I).toNat :=
      Int.natCast_nonneg _
    have hpowNonneg : (0 : Int) ≤ (2 : Int) ^ 255 := by norm_num
    omega
  · rw [if_neg h]
    have hge : EVM.twoPow 255 ≤ (grabDinkWord I).toNat := not_lt.mp h
    have hM : Int.ofNat EVM.wordModulus = (2 : Int) ^ 255 + (2 : Int) ^ 255 := by
      norm_num [EVM.wordModulus, EVM.twoPow]
    have hgeInt : (2 : Int) ^ 255 ≤ Int.ofNat (grabDinkWord I).toNat := by
      change Int.ofNat (EVM.twoPow 255) ≤ Int.ofNat (grabDinkWord I).toNat
      exact Int.ofNat_le.mpr hge
    rw [hM]
    omega

theorem grabDinkInt_hi (I : ExecutionEnv) :
    grabDinkInt I < (2 : Int) ^ 255 := by
  unfold grabDinkInt
  by_cases h : (grabDinkWord I).toNat < EVM.twoPow 255
  · rw [if_pos h]
    change Int.ofNat (grabDinkWord I).toNat < Int.ofNat (EVM.twoPow 255)
    exact Int.ofNat_lt.mpr h
  · rw [if_neg h]
    have hlt : (grabDinkWord I).toNat < EVM.wordModulus := by
      change (grabDinkWord I).val.val < EVM.twoPow 256
      exact (grabDinkWord I).val.isLt
    have hMpos : (0 : Int) < Int.ofNat EVM.wordModulus := by
      norm_num [EVM.wordModulus, EVM.twoPow]
    have hltInt : Int.ofNat (grabDinkWord I).toNat < Int.ofNat EVM.wordModulus := by
      exact Int.ofNat_lt.mpr hlt
    have hpowPos : (0 : Int) < (2 : Int) ^ 255 := by norm_num
    omega

theorem grabDartInt_mod_word (I : ExecutionEnv) :
    grabDartInt I % (Int.ofNat EVM.wordModulus) =
      Int.ofNat (grabDartWord I).toNat := by
  have hltMod :
      Int.ofNat (grabDartWord I).toNat < Int.ofNat EVM.wordModulus := by
    exact Int.ofNat_lt.mpr (by
      change (grabDartWord I).val.val < EVM.twoPow 256
      exact (grabDartWord I).val.isLt)
  have hbase :
      Int.ofNat (grabDartWord I).toNat % Int.ofNat EVM.wordModulus =
        Int.ofNat (grabDartWord I).toNat :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) hltMod
  unfold grabDartInt
  split
  · exact hbase
  · rw [← Int.emod_eq_sub_self_emod]
    exact hbase

theorem grabDartInt_lo (I : ExecutionEnv) :
    -((2 : Int) ^ 255) ≤ grabDartInt I := by
  unfold grabDartInt
  by_cases h : (grabDartWord I).toNat < EVM.twoPow 255
  · rw [if_pos h]
    have hnonneg : (0 : Int) ≤ Int.ofNat (grabDartWord I).toNat :=
      Int.natCast_nonneg _
    have hpowNonneg : (0 : Int) ≤ (2 : Int) ^ 255 := by norm_num
    omega
  · rw [if_neg h]
    have hge : EVM.twoPow 255 ≤ (grabDartWord I).toNat := not_lt.mp h
    have hM : Int.ofNat EVM.wordModulus = (2 : Int) ^ 255 + (2 : Int) ^ 255 := by
      norm_num [EVM.wordModulus, EVM.twoPow]
    have hgeInt : (2 : Int) ^ 255 ≤ Int.ofNat (grabDartWord I).toNat := by
      change Int.ofNat (EVM.twoPow 255) ≤ Int.ofNat (grabDartWord I).toNat
      exact Int.ofNat_le.mpr hge
    rw [hM]
    omega

theorem grabDartInt_hi (I : ExecutionEnv) :
    grabDartInt I < (2 : Int) ^ 255 := by
  unfold grabDartInt
  by_cases h : (grabDartWord I).toNat < EVM.twoPow 255
  · rw [if_pos h]
    change Int.ofNat (grabDartWord I).toNat < Int.ofNat (EVM.twoPow 255)
    exact Int.ofNat_lt.mpr h
  · rw [if_neg h]
    have hlt : (grabDartWord I).toNat < EVM.wordModulus := by
      change (grabDartWord I).val.val < EVM.twoPow 256
      exact (grabDartWord I).val.isLt
    have hltInt : Int.ofNat (grabDartWord I).toNat < Int.ofNat EVM.wordModulus := by
      exact Int.ofNat_lt.mpr hlt
    have hpowPos : (0 : Int) < (2 : Int) ^ 255 := by norm_num
    omega

theorem grabDtab_mod_word (I : ExecutionEnv) (rate : UInt256) :
    (Int.ofNat rate.toNat * grabDartInt I) % (Int.ofNat EVM.wordModulus) =
      Int.ofNat (UInt256.mul (grabDartWord I) rate).toNat := by
  have hrateLt : rate.toNat < EVM.wordModulus := by
    change rate.val.val < EVM.twoPow 256
    exact rate.val.isLt
  calc
    (Int.ofNat rate.toNat * grabDartInt I) % (Int.ofNat EVM.wordModulus)
        = (Int.ofNat rate.toNat % Int.ofNat EVM.wordModulus *
            (grabDartInt I % Int.ofNat EVM.wordModulus)) %
            Int.ofNat EVM.wordModulus := by
          rw [Int.mul_emod]
    _ = (Int.ofNat rate.toNat * Int.ofNat (grabDartWord I).toNat) %
            Int.ofNat EVM.wordModulus := by
          rw [grabDartInt_mod_word]
          have hrateMod :
              Int.ofNat rate.toNat % Int.ofNat EVM.wordModulus =
                Int.ofNat rate.toNat :=
            Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hrateLt)
          rw [hrateMod]
    _ = Int.ofNat ((rate.toNat * (grabDartWord I).toNat) % EVM.wordModulus) := by
          change Int.ofNat (rate.toNat * (grabDartWord I).toNat) %
              Int.ofNat EVM.wordModulus =
            Int.ofNat ((rate.toNat * (grabDartWord I).toNat) % EVM.wordModulus)
          exact (Int.natCast_emod (rate.toNat * (grabDartWord I).toNat)
            EVM.wordModulus).symm
    _ = Int.ofNat (UInt256.mul (grabDartWord I) rate).toNat := by
          rw [u256_mul_toNat]
          rw [Nat.mul_comm rate.toNat (grabDartWord I).toNat]
          rw [show EVM.wordModulus = UInt256.size by rfl]

theorem grab_dtab_word_guard_true_of_rate_zero (I : ExecutionEnv) {rate : UInt256}
    (hrate : rate = ⟨0⟩) :
    grabDartWord I = ⟨0⟩ ∨
      UInt256.eq (UInt256.sdiv (UInt256.mul (grabDartWord I) rate)
        (grabDartWord I)) rate ≠ ⟨0⟩ := by
  by_cases hdart : grabDartWord I = ⟨0⟩
  · exact Or.inl hdart
  · exact Or.inr (by
      rw [hrate, u256_mul_zero_right, u256_sdiv_zero_left, u256_eq_refl]
      native_decide)

theorem grab_dtab_word_guard_true_of_range_pos
    (I : ExecutionEnv) {rate : UInt256}
    (hdartLow : (grabDartWord I).toNat < EVM.twoPow 255)
    (hdartWordNe : grabDartWord I ≠ ⟨0⟩)
    (hprodHi :
      Int.ofNat rate.toNat * grabDartInt I < (2 : Int) ^ 255) :
    grabDartWord I = ⟨0⟩ ∨
      UInt256.eq (UInt256.sdiv (UInt256.mul (grabDartWord I) rate)
        (grabDartWord I)) rate ≠ ⟨0⟩ := by
  right
  have hdartNatPos : 0 < (grabDartWord I).toNat := by
    have hneNat : (grabDartWord I).toNat ≠ 0 := by
      intro hzero
      exact hdartWordNe (uint256_toNat_eq_zero hzero)
    exact Nat.pos_of_ne_zero hneNat
  have hprodInt :
      (Int.ofNat ((grabDartWord I).toNat * rate.toNat)) < (2 : Int) ^ 255 := by
    have hdartInt :
        grabDartInt I = Int.ofNat (grabDartWord I).toNat := by
      unfold grabDartInt
      rw [if_pos hdartLow]
    have h := hprodHi
    rw [hdartInt] at h
    change (((grabDartWord I).toNat * rate.toNat : Nat) : Int) < (2 : Int) ^ 255
    rw [Nat.mul_comm]
    exact h
  have hprodNatSign :
      (grabDartWord I).toNat * rate.toNat < EVM.twoPow 255 := by
    change (grabDartWord I).toNat * rate.toNat < 2 ^ 255
    apply Int.ofNat_lt.mp
    have hpow : ((2 ^ 255 : Nat) : Int) = (2 : Int) ^ 255 := by
      norm_num
    rw [hpow]
    exact hprodInt
  have hprodNatSize :
      (grabDartWord I).toNat * rate.toNat < UInt256.size := by
    have hsignSize : EVM.twoPow 255 < UInt256.size := by
      norm_num [EVM.twoPow, UInt256.size]
    omega
  have hmulToNat :
      (UInt256.mul (grabDartWord I) rate).toNat =
        (grabDartWord I).toNat * rate.toNat := by
    rw [u256_mul_toNat]
    exact Nat.mod_eq_of_lt hprodNatSize
  have hmulLow :
      ¬ EVM.twoPow 255 ≤ (UInt256.mul (grabDartWord I) rate).toNat := by
    rw [hmulToNat]
    omega
  have hdartLowNot :
      ¬ EVM.twoPow 255 ≤ (grabDartWord I).toNat := by
    omega
  have hsdiv :
      UInt256.sdiv (UInt256.mul (grabDartWord I) rate) (grabDartWord I) = rate := by
    unfold UInt256.sdiv
    rw [if_neg]
    · rw [if_neg]
      · apply u256_inj
        change (UInt256.div (UInt256.mul (grabDartWord I) rate)
          (grabDartWord I)).toNat = rate.toNat
        rw [udiv_toNat, hmulToNat]
        exact Nat.mul_div_right rate.toNat hdartNatPos
      · simpa [EVM.twoPow] using hdartLowNot
    · simpa [EVM.twoPow] using hmulLow
  rw [hsdiv, u256_eq_refl]
  native_decide

theorem grab_dtab_word_high_toNat_of_range_neg
    (I : ExecutionEnv) {rate : UInt256}
    (hdartHigh : EVM.twoPow 255 ≤ (grabDartWord I).toNat)
    (hrateNe : rate ≠ ⟨0⟩)
    (hprodLo :
      -((2 : Int) ^ 255) ≤ Int.ofNat rate.toNat * grabDartInt I) :
    (UInt256.mul (grabDartWord I) rate).toNat =
      UInt256.size - ((UInt256.size - (grabDartWord I).toNat) * rate.toNat) := by
  let dabs := UInt256.size - (grabDartWord I).toNat
  have hdartInt : grabDartInt I = - Int.ofNat dabs := by
    unfold grabDartInt
    rw [if_neg (by simpa [EVM.twoPow] using not_lt.mpr hdartHigh)]
    dsimp [dabs]
    have hword : EVM.wordModulus = UInt256.size := by rfl
    rw [hword]
    have hle : (grabDartWord I).toNat ≤ UInt256.size :=
      Nat.le_of_lt (grabDartWord I).val.isLt
    rw [Nat.cast_sub hle]
    omega
  have hdabsPos : 0 < dabs := by
    dsimp [dabs]
    have hlt : (grabDartWord I).toNat < UInt256.size := (grabDartWord I).val.isLt
    omega
  have hratePos : 0 < rate.toNat := by
    have hneNat : rate.toNat ≠ 0 := by
      intro hz
      exact hrateNe (uint256_toNat_eq_zero hz)
    exact Nat.pos_of_ne_zero hneNat
  have hprodLeSign : dabs * rate.toNat ≤ EVM.twoPow 255 := by
    have h := hprodLo
    rw [hdartInt] at h
    exact int_neg_mul_bound_to_nat h
  have hprodBound : dabs * rate.toNat < UInt256.size := by
    exact lt_of_le_of_lt hprodLeSign u256_sign_lt_size
  rw [u256_mul_toNat]
  change (grabDartWord I).toNat * rate.toNat % UInt256.size =
    UInt256.size - dabs * rate.toNat
  have hdartNat : (grabDartWord I).toNat = UInt256.size - dabs := by
    dsimp [dabs]
    omega
  rw [hdartNat]
  exact nat_sub_mul_mod hdabsPos hratePos hprodBound

theorem grab_dtab_word_guard_true_of_range_neg
    (I : ExecutionEnv) {rate : UInt256}
    (hdartHigh : EVM.twoPow 255 ≤ (grabDartWord I).toNat)
    (hrateNe : rate ≠ ⟨0⟩)
    (hprodLo :
      -((2 : Int) ^ 255) ≤ Int.ofNat rate.toNat * grabDartInt I) :
    grabDartWord I = ⟨0⟩ ∨
      UInt256.eq (UInt256.sdiv (UInt256.mul (grabDartWord I) rate)
        (grabDartWord I)) rate ≠ ⟨0⟩ := by
  right
  let dabs := UInt256.size - (grabDartWord I).toNat
  let p := dabs * rate.toNat
  have hpowPos : 0 < EVM.twoPow 255 := by
    change 0 < 2 ^ 255
    exact pow_pos (by decide : (0 : Nat) < 2) 255
  have hdartPos : 0 < (grabDartWord I).toNat :=
    lt_of_lt_of_le hpowPos hdartHigh
  have hdabsPos : 0 < dabs := by
    dsimp [dabs]
    have hlt : (grabDartWord I).toNat < UInt256.size := (grabDartWord I).val.isLt
    omega
  have hratePos : 0 < rate.toNat := by
    have hneNat : rate.toNat ≠ 0 := by
      intro hz
      exact hrateNe (uint256_toNat_eq_zero hz)
    exact Nat.pos_of_ne_zero hneNat
  have hdartInt : grabDartInt I = - Int.ofNat dabs := by
    unfold grabDartInt
    rw [if_neg (by simpa [EVM.twoPow] using not_lt.mpr hdartHigh)]
    dsimp [dabs]
    have hword : EVM.wordModulus = UInt256.size := by rfl
    rw [hword]
    have hle : (grabDartWord I).toNat ≤ UInt256.size :=
      Nat.le_of_lt (grabDartWord I).val.isLt
    rw [Nat.cast_sub hle]
    omega
  have hprodLeSign : p ≤ EVM.twoPow 255 := by
    dsimp [p]
    have h := hprodLo
    rw [hdartInt] at h
    exact int_neg_mul_bound_to_nat h
  have hprodBound : p < UInt256.size :=
    lt_of_le_of_lt hprodLeSign u256_sign_lt_size
  have hprodToNat : (UInt256.mul (grabDartWord I) rate).toNat = UInt256.size - p := by
    dsimp [p, dabs]
    exact grab_dtab_word_high_toNat_of_range_neg I hdartHigh hrateNe hprodLo
  have hprodHigh : EVM.twoPow 255 ≤ (UInt256.mul (grabDartWord I) rate).toNat := by
    rw [hprodToNat, u256_size_eq_two_sign]
    omega
  have hprodPos : 0 < (UInt256.mul (grabDartWord I) rate).toNat :=
    lt_of_lt_of_le hpowPos hprodHigh
  have hAbsDartToNat : (UInt256.abs (grabDartWord I)).toNat = dabs := by
    dsimp [dabs]
    exact u256_abs_high_toNat (by simpa [EVM.twoPow] using hdartHigh) hdartPos
  have hAbsProdToNat :
      (UInt256.abs (UInt256.mul (grabDartWord I) rate)).toNat = p := by
    rw [u256_abs_high_toNat (by simpa [EVM.twoPow] using hprodHigh) hprodPos]
    rw [hprodToNat]
    exact Nat.sub_sub_self (le_of_lt hprodBound)
  have hsdiv :
      UInt256.sdiv (UInt256.mul (grabDartWord I) rate) (grabDartWord I) = rate := by
    unfold UInt256.sdiv
    rw [if_pos (by simpa [EVM.twoPow] using hprodHigh)]
    rw [if_pos (by simpa [EVM.twoPow] using hdartHigh)]
    apply u256_inj
    change (UInt256.div (UInt256.abs (UInt256.mul (grabDartWord I) rate))
      (UInt256.abs (grabDartWord I))).toNat = rate.toNat
    apply u256_div_toNat_eq_of_toNat (denom := dabs)
    · rw [hAbsProdToNat]
    · exact hAbsDartToNat
    · exact hdabsPos
  rw [hsdiv, u256_eq_refl]
  native_decide

theorem grabDartInt_eq_of_low (I : ExecutionEnv)
    (hlow : (grabDartWord I).toNat < EVM.twoPow 255) :
    grabDartInt I = Int.ofNat (grabDartWord I).toNat := by
  unfold grabDartInt
  rw [if_pos hlow]

theorem grabDartInt_eq_of_high (I : ExecutionEnv)
    (hhigh : EVM.twoPow 255 ≤ (grabDartWord I).toNat) :
    grabDartInt I =
      Int.ofNat (grabDartWord I).toNat - Int.ofNat EVM.wordModulus := by
  unfold grabDartInt
  rw [if_neg (by simpa [EVM.twoPow] using not_lt.mpr hhigh)]

theorem grabDartInt_pos_of_low_ne (I : ExecutionEnv)
    (hlow : (grabDartWord I).toNat < EVM.twoPow 255)
    (hword : grabDartWord I ≠ ⟨0⟩) :
    0 < grabDartInt I := by
  rw [grabDartInt_eq_of_low I hlow]
  apply Int.natCast_pos.mpr
  have hneNat : (grabDartWord I).toNat ≠ 0 := by
    intro hzero
    exact hword (uint256_toNat_eq_zero hzero)
  exact Nat.pos_of_ne_zero hneNat

theorem grabDartInt_neg_of_high (I : ExecutionEnv)
    (hhigh : EVM.twoPow 255 ≤ (grabDartWord I).toNat) :
    grabDartInt I < 0 := by
  rw [grabDartInt_eq_of_high I hhigh]
  have hlt : Int.ofNat (grabDartWord I).toNat < Int.ofNat EVM.wordModulus := by
    have hltNat : (grabDartWord I).toNat < EVM.wordModulus := by
      change (grabDartWord I).val.val < EVM.twoPow 256
      exact (grabDartWord I).val.isLt
    exact Int.ofNat_lt.mpr hltNat
  exact sub_neg.mpr hlt

theorem grabDartInt_zero_of_word_zero (I : ExecutionEnv)
    (hword : grabDartWord I = ⟨0⟩) :
    grabDartInt I = 0 := by
  unfold grabDartInt
  rw [hword]
  simp [EVM.twoPow]

theorem grabDartInt_ne_zero_of_word_ne (I : ExecutionEnv)
    (hword : grabDartWord I ≠ ⟨0⟩) :
    grabDartInt I ≠ 0 := by
  by_cases hlow : (grabDartWord I).toNat < EVM.twoPow 255
  · rw [grabDartInt_eq_of_low I hlow]
    intro hzero
    apply hword
    apply uint256_toNat_eq_zero
    exact Int.ofNat_eq_zero.mp hzero
  · have hhigh : EVM.twoPow 255 ≤ (grabDartWord I).toNat := not_lt.mp hlow
    have hneg := grabDartInt_neg_of_high I hhigh
    omega

theorem grab_dtab_word_range_hi_of_guard_pos
    (I : ExecutionEnv) {rate : UInt256}
    (hdartLow : (grabDartWord I).toNat < EVM.twoPow 255)
    (hrateLow : rate.toNat < EVM.twoPow 255)
    (hrateNe : rate ≠ ⟨0⟩)
    (hsdiv :
      UInt256.sdiv (UInt256.mul (grabDartWord I) rate) (grabDartWord I) = rate) :
    (UInt256.mul (grabDartWord I) rate).toNat < EVM.twoPow 255 := by
  by_contra hnot
  have hprodHigh : EVM.twoPow 255 ≤ (UInt256.mul (grabDartWord I) rate).toNat :=
    not_lt.mp hnot
  have hprodPos : 0 < (UInt256.mul (grabDartWord I) rate).toNat := by
    have hpow : 0 < EVM.twoPow 255 := by
      change 0 < 2 ^ 255
      exact pow_pos (by decide : (0 : Nat) < 2) 255
    exact lt_of_lt_of_le hpow hprodHigh
  let q := UInt256.div (UInt256.abs (UInt256.mul (grabDartWord I) rate))
    (grabDartWord I)
  have hqLe : q.toNat ≤ EVM.twoPow 255 := by
    dsimp [q]
    rw [udiv_toNat]
    have habs :
        (UInt256.abs (UInt256.mul (grabDartWord I) rate)).toNat =
          UInt256.size - (UInt256.mul (grabDartWord I) rate).toNat :=
      u256_abs_high_toNat hprodHigh hprodPos
    rw [habs]
    have hsub :
        UInt256.size - (UInt256.mul (grabDartWord I) rate).toNat ≤
          EVM.twoPow 255 := by
      rw [u256_size_eq_two_sign]
      omega
    exact le_trans (Nat.div_le_self _ _) hsub
  have hs := u256_sdiv_high_low (prod := UInt256.mul (grabDartWord I) rate)
    (rate := grabDartWord I) hprodHigh hdartLow
  rw [hs] at hsdiv
  cases rate with
  | mk rval =>
      dsimp [UInt256.toNat] at hrateLow
      dsimp [q] at hqLe hsdiv
      generalize hq :
        UInt256.div (UInt256.abs (UInt256.mul (grabDartWord I) { val := rval }))
            (grabDartWord I) = qword at hqLe hsdiv
      cases qword with
      | mk qval =>
          have hnegVal : (qval * (-1 : Fin UInt256.size)).val = rval.val := by
            injection hsdiv with hv
            exact congrArg Fin.val hv
          exact fin_uint256_mul_neg_one_val_low_contra
            (q := { val := qval }) (art := { val := rval }) hqLe hrateLow
            hrateNe hnegVal

set_option maxHeartbeats 0 in
theorem grab_dtab_product_hi_of_guard_pos
    (I : ExecutionEnv) {rate : UInt256}
    (hdartLow : (grabDartWord I).toNat < EVM.twoPow 255)
    (hrateLow : rate.toNat < EVM.twoPow 255)
    (hrateNe : rate ≠ ⟨0⟩)
    (hsdiv :
      UInt256.sdiv (UInt256.mul (grabDartWord I) rate) (grabDartWord I) = rate) :
    Int.ofNat rate.toNat * grabDartInt I < (2 : Int) ^ 255 := by
  have hprodLow : (UInt256.mul (grabDartWord I) rate).toNat < EVM.twoPow 255 :=
    grab_dtab_word_range_hi_of_guard_pos I hdartLow hrateLow hrateNe hsdiv
  have hprodLowNot :
      ¬ EVM.twoPow 255 ≤ (UInt256.mul (grabDartWord I) rate).toNat := by
    omega
  have hdartLowNot : ¬ EVM.twoPow 255 ≤ (grabDartWord I).toNat := by
    omega
  have hsdivEq :
      UInt256.div (UInt256.mul (grabDartWord I) rate) (grabDartWord I) = rate := by
    unfold UInt256.sdiv at hsdiv
    rw [if_neg (by simpa [EVM.twoPow] using hprodLowNot)] at hsdiv
    rw [if_neg (by simpa [EVM.twoPow] using hdartLowNot)] at hsdiv
    exact hsdiv
  have hdivNat :
      (UInt256.mul (grabDartWord I) rate).toNat / (grabDartWord I).toNat =
        rate.toNat := by
    have h := congrArg UInt256.toNat hsdivEq
    simpa [udiv_toNat] using h
  let P := (grabDartWord I).toNat * rate.toNat
  have hmulMod : (UInt256.mul (grabDartWord I) rate).toNat = P % UInt256.size := by
    dsimp [P]
    rw [u256_mul_toNat]
  have hleDiv :
      rate.toNat ≤
        (UInt256.mul (grabDartWord I) rate).toNat / (grabDartWord I).toNat := by
    rw [hdivNat]
  have hPLeMod : P ≤ P % UInt256.size := by
    dsimp [P]
    rw [← hmulMod]
    have hle := Nat.mul_le_of_le_div (grabDartWord I).toNat rate.toNat
      (UInt256.mul (grabDartWord I) rate).toNat hleDiv
    simpa [Nat.mul_comm] using hle
  have hPEqMod : P = P % UInt256.size :=
    le_antisymm hPLeMod (Nat.mod_le P UInt256.size)
  have hPLtSign : P < EVM.twoPow 255 := by
    rw [hPEqMod]
    rw [← hmulMod]
    exact hprodLow
  dsimp [P] at hPLtSign
  rw [grabDartInt_eq_of_low I hdartLow]
  have hcast :
      ((rate.toNat * (grabDartWord I).toNat : Nat) : Int) < (2 : Int) ^ 255 := by
    rw [Nat.mul_comm]
    exact_mod_cast (by simpa [EVM.twoPow] using hPLtSign)
  change ((rate.toNat * (grabDartWord I).toNat : Nat) : Int) < (2 : Int) ^ 255
  exact hcast

set_option maxHeartbeats 0 in
theorem grab_dtab_word_neg_low_product_contra
    (I : ExecutionEnv) {rate : UInt256}
    (hdartHigh : EVM.twoPow 255 ≤ (grabDartWord I).toNat)
    (hprodLow : (UInt256.mul (grabDartWord I) rate).toNat < EVM.twoPow 255)
    (hrateLow : rate.toNat < EVM.twoPow 255)
    (hrateNe : rate ≠ ⟨0⟩)
    (hsdiv :
      UInt256.sdiv (UInt256.mul (grabDartWord I) rate) (grabDartWord I) = rate) :
    False := by
  have hdartHighIf : 2 ^ 255 ≤ (grabDartWord I).toNat := by
    simpa [EVM.twoPow] using hdartHigh
  have hprodHighNot : ¬ 2 ^ 255 ≤ (UInt256.mul (grabDartWord I) rate).toNat := by
    simpa [EVM.twoPow] using not_le.mpr hprodLow
  have hs := hsdiv
  unfold UInt256.sdiv at hs
  rw [if_neg hprodHighNot] at hs
  rw [if_pos hdartHighIf] at hs
  let q := (UInt256.mul (grabDartWord I) rate) / (UInt256.abs (grabDartWord I))
  have hqLe : q.toNat ≤ EVM.twoPow 255 := by
    dsimp [q]
    change (UInt256.div (UInt256.mul (grabDartWord I) rate)
      (UInt256.abs (grabDartWord I))).toNat ≤ EVM.twoPow 255
    rw [udiv_toNat]
    exact le_trans (Nat.div_le_self _ _) (le_of_lt hprodLow)
  cases rate with
  | mk rval =>
      dsimp [UInt256.toNat] at hrateLow
      dsimp [q] at hqLe hs
      generalize hqwordEq :
        ((UInt256.mul (grabDartWord I) { val := rval }) /
          (UInt256.abs (grabDartWord I))) = qword at hqLe hs
      cases qword with
      | mk qval =>
          have hnegVal : (qval * (-1 : Fin UInt256.size)).val = rval.val := by
            injection hs with hv
            exact congrArg Fin.val hv
          exact fin_uint256_mul_neg_one_val_low_contra
            (q := { val := qval }) (art := { val := rval }) hqLe hrateLow
            hrateNe hnegVal

set_option maxHeartbeats 0 in
theorem grab_dtab_product_lo_of_guard_neg
    (I : ExecutionEnv) {rate : UInt256}
    (hdartHigh : EVM.twoPow 255 ≤ (grabDartWord I).toNat)
    (hrateLow : rate.toNat < EVM.twoPow 255)
    (hrateNe : rate ≠ ⟨0⟩)
    (hsdiv :
      UInt256.sdiv (UInt256.mul (grabDartWord I) rate) (grabDartWord I) = rate) :
    -((2 : Int) ^ 255) ≤ Int.ofNat rate.toNat * grabDartInt I := by
  let dabs := UInt256.size - (grabDartWord I).toNat
  let prod := UInt256.mul (grabDartWord I) rate
  have hpowPos : 0 < EVM.twoPow 255 := by
    change 0 < 2 ^ 255
    exact pow_pos (by decide : (0 : Nat) < 2) 255
  have hdartPos : 0 < (grabDartWord I).toNat :=
    lt_of_lt_of_le hpowPos hdartHigh
  have hdartInt : grabDartInt I = - Int.ofNat dabs := by
    unfold grabDartInt
    rw [if_neg (by simpa [EVM.twoPow] using not_lt.mpr hdartHigh)]
    dsimp [dabs]
    have hword : EVM.wordModulus = UInt256.size := by rfl
    rw [hword]
    have hle : (grabDartWord I).toNat ≤ UInt256.size :=
      Nat.le_of_lt (grabDartWord I).val.isLt
    rw [Nat.cast_sub hle]
    omega
  have hAbsDartToNat : (UInt256.abs (grabDartWord I)).toNat = dabs := by
    dsimp [dabs]
    exact u256_abs_high_toNat (by simpa [EVM.twoPow] using hdartHigh) hdartPos
  have hprodHigh : EVM.twoPow 255 ≤ prod.toNat := by
    by_contra hnot
    have hprodLow : prod.toNat < EVM.twoPow 255 := by
      omega
    exact grab_dtab_word_neg_low_product_contra I hdartHigh
      (by simpa [prod] using hprodLow) hrateLow hrateNe
      (by simpa [prod] using hsdiv)
  have hprodPos : 0 < prod.toNat :=
    lt_of_lt_of_le hpowPos hprodHigh
  have hdartHighIf : 2 ^ 255 ≤ (grabDartWord I).toNat := by
    simpa [EVM.twoPow] using hdartHigh
  have hsdivEq :
      UInt256.div (UInt256.abs prod) (UInt256.abs (grabDartWord I)) = rate := by
    unfold UInt256.sdiv at hsdiv
    rw [if_pos (by simpa [EVM.twoPow, prod] using hprodHigh)] at hsdiv
    rw [if_pos hdartHighIf] at hsdiv
    simpa [prod] using hsdiv
  have hpLeSign : dabs * rate.toNat ≤ EVM.twoPow 255 :=
    u256_abs_div_eq_bound_to_sign (rate := grabDartWord I) (prod := prod)
      (art := rate) hAbsDartToNat hprodHigh hprodPos hsdivEq
  rw [hdartInt]
  have hp : ((dabs * rate.toNat : Nat) : Int) ≤ (2 : Int) ^ 255 := by
    exact_mod_cast (by simpa [EVM.twoPow] using hpLeSign)
  have hmul :
      Int.ofNat rate.toNat * -Int.ofNat dabs =
        -((dabs * rate.toNat : Nat) : Int) := by
    calc
      Int.ofNat rate.toNat * -Int.ofNat dabs =
          -(Int.ofNat rate.toNat * Int.ofNat dabs) := by ring
      _ = -((rate.toNat * dabs : Nat) : Int) := by
          exact congrArg Neg.neg (Nat.cast_mul rate.toNat dabs).symm
      _ = -((dabs * rate.toNat : Nat) : Int) := by rw [Nat.mul_comm]
  rw [hmul]
  omega

set_option maxHeartbeats 0 in
theorem grab_dtab_product_range_of_guard
    (I : ExecutionEnv) {rate : UInt256}
    (hrateLow : rate.toNat < EVM.twoPow 255)
    (hguard :
      grabDartWord I = ⟨0⟩ ∨
        UInt256.sdiv (UInt256.mul (grabDartWord I) rate) (grabDartWord I) = rate) :
    -((2 : Int) ^ 255) ≤ Int.ofNat rate.toNat * grabDartInt I ∧
      Int.ofNat rate.toNat * grabDartInt I < (2 : Int) ^ 255 := by
  by_cases hdartZero : grabDartWord I = ⟨0⟩
  · have hdartIntZero : grabDartInt I = 0 := by
      unfold grabDartInt
      rw [hdartZero]
      decide
    constructor <;> rw [hdartIntZero] <;> norm_num
  · have hsdiv : UInt256.sdiv (UInt256.mul (grabDartWord I) rate) (grabDartWord I) = rate := by
      cases hguard with
      | inl hzero => exact False.elim (hdartZero hzero)
      | inr hs => exact hs
    constructor
    · by_cases hdartLow : (grabDartWord I).toNat < EVM.twoPow 255
      · have hdartPos := grabDartInt_pos_of_low_ne I hdartLow hdartZero
        have hsignPos : 0 < (2 : Int) ^ 255 := by norm_num
        have hrateNonneg : 0 ≤ Int.ofNat rate.toNat := Int.natCast_nonneg _
        nlinarith
      · by_cases hrateZero : rate = ⟨0⟩
        · have hrateNatZero : rate.toNat = 0 := by
            rw [hrateZero]
            rfl
          have hprodZero : Int.ofNat rate.toNat * grabDartInt I = 0 := by
            rw [hrateNatZero]
            ring
          have hpowNonneg : (0 : Int) ≤ (2 : Int) ^ 255 := by positivity
          calc
            -((2 : Int) ^ 255) ≤ 0 := by omega
            _ = Int.ofNat rate.toNat * grabDartInt I := hprodZero.symm
        · exact grab_dtab_product_lo_of_guard_neg I (not_lt.mp hdartLow)
            hrateLow hrateZero hsdiv
    · by_cases hdartLow : (grabDartWord I).toNat < EVM.twoPow 255
      · by_cases hrateZero : rate = ⟨0⟩
        · have hrateNatZero : rate.toNat = 0 := by
            rw [hrateZero]
            rfl
          have hprodZero : Int.ofNat rate.toNat * grabDartInt I = 0 := by
            rw [hrateNatZero]
            ring
          rw [hprodZero]
          positivity
        · exact grab_dtab_product_hi_of_guard_pos I hdartLow hrateLow hrateZero hsdiv
      · have hdartNeg := grabDartInt_neg_of_high I (not_lt.mp hdartLow)
        have hsignPos : 0 < (2 : Int) ^ 255 := by norm_num
        have hrateNonneg : 0 ≤ Int.ofNat rate.toNat := Int.natCast_nonneg _
        nlinarith

theorem grabDinkAddGuardNegCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      UInt256.slt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩) :
    0 ≤ grabDinkInt I ∨ new.toNat ≤ old.toNat := by
  cases h with
  | inl hslt =>
      exact Or.inl (slt_zero_eq_zero_to_nonneg (grabDinkWord I) hslt)
  | inr hgt =>
      exact Or.inr (ugt_eq_zero_to_le hgt)

theorem grabDinkAddGuardPosCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      UInt256.sgt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩) :
    grabDinkInt I ≤ 0 ∨ old.toNat ≤ new.toNat := by
  cases h with
  | inl hsgt =>
      exact Or.inl (sgt_zero_eq_zero_to_nonpos (grabDinkWord I) hsgt)
  | inr hlt =>
      exact Or.inr (ult_eq_zero_to_le hlt)

theorem grabDartAddGuardNegCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      UInt256.slt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩) :
    0 ≤ grabDartInt I ∨ new.toNat ≤ old.toNat := by
  cases h with
  | inl hslt =>
      exact Or.inl (slt_zero_eq_zero_to_nonneg (grabDartWord I) hslt)
  | inr hgt =>
      exact Or.inr (ugt_eq_zero_to_le hgt)

theorem grabDartAddGuardPosCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      UInt256.sgt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩) :
    grabDartInt I ≤ 0 ∨ old.toNat ≤ new.toNat := by
  cases h with
  | inl hsgt =>
      exact Or.inl (sgt_zero_eq_zero_to_nonpos (grabDartWord I) hsgt)
  | inr hlt =>
      exact Or.inr (ult_eq_zero_to_le hlt)

theorem grabDinkSubGuardNegCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      UInt256.sgt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩) :
    grabDinkInt I ≤ 0 ∨ new.toNat ≤ old.toNat := by
  cases h with
  | inl hsgt =>
      exact Or.inl (sgt_zero_eq_zero_to_nonpos (grabDinkWord I) hsgt)
  | inr hgt =>
      exact Or.inr (ugt_eq_zero_to_le hgt)

theorem grabDinkSubGuardPosCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      UInt256.slt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩) :
    0 ≤ grabDinkInt I ∨ old.toNat ≤ new.toNat := by
  cases h with
  | inl hslt =>
      exact Or.inl (slt_zero_eq_zero_to_nonneg (grabDinkWord I) hslt)
  | inr hlt =>
      exact Or.inr (ult_eq_zero_to_le hlt)

theorem grabDinkSubGuardNegFailCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      ¬ (UInt256.sgt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩)) :
    0 < grabDinkInt I ∧ old.toNat < new.toNat := by
  constructor
  · exact sgt_zero_ne_zero_to_pos (grabDinkWord I) (by
      intro hsgt
      exact h (Or.inl hsgt))
  · exact ugt_ne_zero_to_gt (by
      intro hgt
      exact h (Or.inr hgt))

theorem grabDinkSubGuardPosFailCond {I : ExecutionEnv} {old new : UInt256}
    (h :
      ¬ (UInt256.slt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩)) :
    grabDinkInt I < 0 ∧ new.toNat < old.toNat := by
  constructor
  · exact slt_zero_ne_zero_to_neg (grabDinkWord I) (by
      intro hslt
      exact h (Or.inl hslt))
  · exact ult_ne_zero_to_lt (by
      intro hlt
      exact h (Or.inr hlt))

theorem grabDtabSubGuardNegCond {dtab : Int} {dtabWord old new : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ dtab)
    (hhi : dtab < (2 : Int) ^ 255)
    (hmod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (h :
      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩) :
    dtab ≤ 0 ∨ new.toNat ≤ old.toNat := by
  cases h with
  | inl hsgt =>
      exact Or.inl (int_nonpos_of_word_sgt_zero hlo hhi hmod hsgt)
  | inr hgt =>
      exact Or.inr (ugt_eq_zero_to_le hgt)

theorem grabDtabSubGuardPosCond {dtab : Int} {dtabWord old new : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ dtab)
    (hhi : dtab < (2 : Int) ^ 255)
    (hmod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (h :
      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩) :
    0 ≤ dtab ∨ old.toNat ≤ new.toNat := by
  cases h with
  | inl hslt =>
      exact Or.inl (int_nonneg_of_word_slt_zero hlo hhi hmod hslt)
  | inr hlt =>
      exact Or.inr (ult_eq_zero_to_le hlt)

theorem grabDtabSubGuardNegFailCond {dtab : Int} {dtabWord old new : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ dtab)
    (hhi : dtab < (2 : Int) ^ 255)
    (hmod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (h :
      ¬ (UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt new old = ⟨0⟩)) :
    0 < dtab ∧ old.toNat < new.toNat := by
  constructor
  · exact int_pos_of_word_sgt_ne_zero hlo hhi hmod (by
      intro hsgt
      exact h (Or.inl hsgt))
  · exact ugt_ne_zero_to_gt (by
      intro hgt
      exact h (Or.inr hgt))

theorem grabDtabSubGuardPosFailCond {dtab : Int} {dtabWord old new : UInt256}
    (hlo : -((2 : Int) ^ 255) ≤ dtab)
    (hhi : dtab < (2 : Int) ^ 255)
    (hmod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (h :
      ¬ (UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt new old = ⟨0⟩)) :
    dtab < 0 ∧ new.toNat < old.toNat := by
  constructor
  · exact int_neg_of_word_slt_ne_zero hlo hhi hmod (by
      intro hslt
      exact h (Or.inl hslt))
  · exact ult_ne_zero_to_lt (by
      intro hlt
      exact h (Or.inr hlt))

abbrev grabIValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev grabUValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (grabUWord I).toNat)

abbrev grabVValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (grabVWord I).toNat)

abbrev grabWValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (grabWWord I).toNat)

abbrev grabDinkValue (I : ExecutionEnv) : Value :=
  .int (grabDinkInt I)

abbrev grabDartValue (I : ExecutionEnv) : Value :=
  .int (grabDartInt I)

abbrev grabStore (I : ExecutionEnv) : Store :=
  ((((((∅ : Store).insert "i" (grabIValue I)).insert "u" (grabUValue I)).insert
    "v" (grabVValue I)).insert "w" (grabWValue I)).insert "dink" (grabDinkValue I)).insert
    "dart" (grabDartValue I)

abbrev grabIKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev grabUKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (grabUWord I).toNat)

abbrev grabVKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (grabVWord I).toNat)

abbrev grabWKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (grabWWord I).toNat)

abbrev grabStoreUrnInkNew (I : ExecutionEnv) (urnInkNew : UInt256) : Store :=
  (grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))

abbrev grabStoreUrnArtNew (I : ExecutionEnv) (urnInkNew urnArtNew : UInt256) : Store :=
  (grabStoreUrnInkNew I urnInkNew).insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))

abbrev grabStoreIlkArtNew (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) : Store :=
  (grabStoreUrnArtNew I urnInkNew urnArtNew).insert "ilkArtNew"
    (.int (Int.ofNat ilkArtNew.toNat))

abbrev grabStoreDtab (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int) : Store :=
  (grabStoreIlkArtNew I urnInkNew urnArtNew ilkArtNew).insert "dtab"
    (.int dtab)

abbrev grabStoreGemNew (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int) (gemNew : UInt256) : Store :=
  (grabStoreDtab I urnInkNew urnArtNew ilkArtNew dtab).insert "gemNew"
    (.int (Int.ofNat gemNew.toNat))

abbrev grabStoreSinNew (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int) (gemNew sinNew : UInt256) :
    Store :=
  (grabStoreGemNew I urnInkNew urnArtNew ilkArtNew dtab gemNew).insert "sinNew"
    (.int (Int.ofNat sinNew.toNat))

abbrev grabStoreViceNew (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int)
    (gemNew sinNew viceNew : UInt256) : Store :=
  (grabStoreSinNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew).insert "viceNew"
    (.int (Int.ofNat viceNew.toNat))

abbrev grabUrnInkEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "urns", steps := [.mindex (grabIKey I), .mindex (grabUKey I), .field "ink"] }

abbrev grabUrnArtEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "urns", steps := [.mindex (grabIKey I), .mindex (grabUKey I), .field "art"] }

abbrev grabIlkArtEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (grabIKey I), .field "Art"] }

abbrev grabIlkRateEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (grabIKey I), .field "rate"] }

abbrev grabGemEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "gem", steps := [.mindex (grabIKey I), .mindex (grabVKey I)] }

abbrev grabSinEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sin", steps := [.mindex (grabWKey I)] }

abbrev grabViceEvaledRef : EvaledStorageRef :=
  { base := "vice", steps := [] }

theorem grabStore_get_i (I : ExecutionEnv) :
    (grabStore I).get? "i" = some (grabIValue I) := by
  unfold grabStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_self]

theorem grabStore_get_u (I : ExecutionEnv) :
    (grabStore I).get? "u" = some (grabUValue I) := by
  unfold grabStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_self]

theorem grabStore_get_v (I : ExecutionEnv) :
    (grabStore I).get? "v" = some (grabVValue I) := by
  unfold grabStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_self]

theorem grabStore_get_w (I : ExecutionEnv) :
    (grabStore I).get? "w" = some (grabWValue I) := by
  unfold grabStore
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_self]

theorem grabStore_get_dink (I : ExecutionEnv) :
    (grabStore I).get? "dink" = some (grabDinkValue I) := by
  unfold grabStore
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_self]

theorem grabStore_get_dart (I : ExecutionEnv) :
    (grabStore I).get? "dart" = some (grabDartValue I) := by
  simp [grabStore]

theorem grabStore_urns (I : ExecutionEnv) :
    (grabStore I).get? "urns" = none := by
  simp [grabStore]

theorem grabStoreIlkArtNew_get_i (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) :
    (grabStoreIlkArtNew I urnInkNew urnArtNew ilkArtNew).get? "i" =
      some (grabIValue I) := by
  unfold grabStoreIlkArtNew grabStoreUrnArtNew grabStoreUrnInkNew
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  exact grabStore_get_i I

theorem grabStoreIlkArtNew_get_dart (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) :
    (grabStoreIlkArtNew I urnInkNew urnArtNew ilkArtNew).get? "dart" =
      some (grabDartValue I) := by
  unfold grabStoreIlkArtNew grabStoreUrnArtNew grabStoreUrnInkNew
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  exact grabStore_get_dart I

theorem grabStoreIlkArtNew_ilks (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) :
    (grabStoreIlkArtNew I urnInkNew urnArtNew ilkArtNew).get? "ilks" = none := by
  unfold grabStoreIlkArtNew grabStoreUrnArtNew grabStoreUrnInkNew
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  simp [grabStore]

theorem grabStoreDtab_get_i (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int) :
    (grabStoreDtab I urnInkNew urnArtNew ilkArtNew dtab).get? "i" =
      some (grabIValue I) := by
  unfold grabStoreDtab
  rw [store_get_ne _ _ (by native_decide)]
  exact grabStoreIlkArtNew_get_i I urnInkNew urnArtNew ilkArtNew

theorem grabStoreDtab_get_dart (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int) :
    (grabStoreDtab I urnInkNew urnArtNew ilkArtNew dtab).get? "dart" =
      some (grabDartValue I) := by
  unfold grabStoreDtab
  rw [store_get_ne _ _ (by native_decide)]
  exact grabStoreIlkArtNew_get_dart I urnInkNew urnArtNew ilkArtNew

theorem grabStoreDtab_get_dtab (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int) :
    (grabStoreDtab I urnInkNew urnArtNew ilkArtNew dtab).get? "dtab" =
      some (.int dtab) := by
  simp [grabStoreDtab]

theorem grabStoreDtab_ilks (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int) :
    (grabStoreDtab I urnInkNew urnArtNew ilkArtNew dtab).get? "ilks" = none := by
  unfold grabStoreDtab
  rw [store_get_ne _ _ (by native_decide)]
  exact grabStoreIlkArtNew_ilks I urnInkNew urnArtNew ilkArtNew

theorem grabStoreDtab_get_v (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int) :
    (grabStoreDtab I urnInkNew urnArtNew ilkArtNew dtab).get? "v" =
      some (grabVValue I) := by
  unfold grabStoreDtab
  rw [store_get_ne _ _ (by native_decide)]
  unfold grabStoreIlkArtNew grabStoreUrnArtNew grabStoreUrnInkNew
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  exact grabStore_get_v I

theorem grabStoreDtab_get_dink (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int) :
    (grabStoreDtab I urnInkNew urnArtNew ilkArtNew dtab).get? "dink" =
      some (grabDinkValue I) := by
  unfold grabStoreDtab
  rw [store_get_ne _ _ (by native_decide)]
  unfold grabStoreIlkArtNew grabStoreUrnArtNew grabStoreUrnInkNew
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  exact grabStore_get_dink I

theorem grabStoreDtab_gem (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int) :
    (grabStoreDtab I urnInkNew urnArtNew ilkArtNew dtab).get? "gem" = none := by
  unfold grabStoreDtab
  rw [store_get_ne _ _ (by native_decide)]
  unfold grabStoreIlkArtNew grabStoreUrnArtNew grabStoreUrnInkNew
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  simp [grabStore]

theorem grabStoreGemNew_get_w (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int) (gemNew : UInt256) :
    (grabStoreGemNew I urnInkNew urnArtNew ilkArtNew dtab gemNew).get? "w" =
      some (grabWValue I) := by
  unfold grabStoreGemNew
  rw [store_get_ne _ _ (by native_decide)]
  unfold grabStoreDtab grabStoreIlkArtNew grabStoreUrnArtNew grabStoreUrnInkNew
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  exact grabStore_get_w I

theorem grabStoreGemNew_get_dtab (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int) (gemNew : UInt256) :
    (grabStoreGemNew I urnInkNew urnArtNew ilkArtNew dtab gemNew).get? "dtab" =
      some (.int dtab) := by
  unfold grabStoreGemNew
  rw [store_get_ne _ _ (by native_decide)]
  exact grabStoreDtab_get_dtab I urnInkNew urnArtNew ilkArtNew dtab

theorem grabStoreGemNew_sin (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int) (gemNew : UInt256) :
    (grabStoreGemNew I urnInkNew urnArtNew ilkArtNew dtab gemNew).get? "sin" = none := by
  unfold grabStoreGemNew
  rw [store_get_ne _ _ (by native_decide)]
  unfold grabStoreDtab grabStoreIlkArtNew grabStoreUrnArtNew grabStoreUrnInkNew
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  simp [grabStore]

theorem grabStoreSinNew_get_dtab (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int)
    (gemNew sinNew : UInt256) :
    (grabStoreSinNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew).get? "dtab" =
      some (.int dtab) := by
  unfold grabStoreSinNew
  rw [store_get_ne _ _ (by native_decide)]
  exact grabStoreGemNew_get_dtab I urnInkNew urnArtNew ilkArtNew dtab gemNew

theorem grabStoreSinNew_vice (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int)
    (gemNew sinNew : UInt256) :
    (grabStoreSinNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew).get? "vice" =
      none := by
  unfold grabStoreSinNew
  rw [store_get_ne _ _ (by native_decide)]
  unfold grabStoreGemNew grabStoreDtab grabStoreIlkArtNew grabStoreUrnArtNew
    grabStoreUrnInkNew
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  simp [grabStore]

theorem evalExpr_grab_dtab_mul_guard_dart_zero_true
    {evm : EVM.State} {locals : Store} (I : ExecutionEnv) {dtab : Int}
    (hdart : locals.get? "dart" = some (grabDartValue I))
    (hzero : grabDartInt I = 0) :
    evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) } evm
      (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
        (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
          (.storage (ilksF (.var "i") "rate")))) =
      .ok (.bool true) := by
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) } evm
        (.var "dart") = .ok (.int 0) := by
    have hget :
        (locals.insert "dtab" (.int dtab)).get? "dart" =
          some (grabDartValue I) := by
      rw [store_get_ne _ _ (by native_decide)]
      exact hdart
    simpa [grabDartValue, hzero] using vatEvalExpr_varInt hget
  have hleft :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) } evm
        (.binary .eq (.var "dart") (.intLit 0)) = .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind, hdartEval, evalBinaryOp?]
  exact vatEvalExpr_or_true_left hleft

theorem evalExpr_grab_dtab_mul_guard_exact_true
    {evm : EVM.State} {locals : Store} (I : ExecutionEnv) {rate : UInt256} {dtab : Int}
    (hdart : locals.get? "dart" = some (grabDartValue I))
    (hrate :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) } evm
        (.storage (ilksF (.var "i") "rate")) = .ok (.int (Int.ofNat rate.toNat)))
    (hdartNe : grabDartInt I ≠ 0)
    (hdiv : dtab / grabDartInt I = Int.ofNat rate.toNat) :
    evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) } evm
      (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
        (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
          (.storage (ilksF (.var "i") "rate")))) =
      .ok (.bool true) := by
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) } evm
        (.var "dart") = .ok (.int (grabDartInt I)) := by
    have hget :
        (locals.insert "dtab" (.int dtab)).get? "dart" =
          some (grabDartValue I) := by
      rw [store_get_ne _ _ (by native_decide)]
      exact hdart
    exact vatEvalExpr_varInt (by simpa [grabDartValue] using hget)
  have hdtabEval :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) } evm
        (.var "dtab") = .ok (.int dtab) :=
    vatEvalExpr_varInt (by simp)
  have hleft :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) } evm
        (.binary .eq (.var "dart") (.intLit 0)) = .ok (.bool false) := by
    simp [evalExpr?, EvalResult.bind, bind, hdartEval, evalBinaryOp?, hdartNe]
  have hright :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) } evm
        (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
          (.storage (ilksF (.var "i") "rate"))) =
      .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind, hdtabEval, hdartEval, hrate,
      evalBinaryOp?, hdartNe, hdiv]
  exact vatEvalExpr_or_false_right hleft hright

def grabUrnSourceBase (I : ExecutionEnv) : UInt256 :=
  urnsBase (grabIKey I) (grabUKey I)

def grabUrnInkSourceSlot (I : ExecutionEnv) : UInt256 :=
  grabUrnSourceBase I

def grabUrnArtSourceSlot (I : ExecutionEnv) : UInt256 :=
  grabUrnSourceBase I + ⟨1⟩

def grabIlkSourceBase (I : ExecutionEnv) : UInt256 :=
  ilksBase (grabIKey I)

def grabIlkArtSourceSlot (I : ExecutionEnv) : UInt256 :=
  grabIlkSourceBase I

def grabIlkRateSourceSlot (I : ExecutionEnv) : UInt256 :=
  grabIlkSourceBase I + ⟨1⟩

def grabGemSourceBase (I : ExecutionEnv) : UInt256 :=
  gemIlkSlot (grabIKey I)

def grabGemSourceSlot (I : ExecutionEnv) : UInt256 :=
  gemSlot (grabIKey I) (grabVKey I)

def grabSinSourceSlot (I : ExecutionEnv) : UInt256 :=
  sinSlot (grabWKey I)

def grabViceSourceSlot : UInt256 :=
  ⟨8⟩

abbrev grabSourceEvm0 cA gh bl σ σ₀ A I (g : UInt256) :=
  initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I

abbrev grabSourceEvm1 cA gh bl σ σ₀ A I (g : UInt256) (urnInkNew : UInt256) :=
  let evm0 := grabSourceEvm0 cA gh bl σ σ₀ A I g
  Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
    (grabUrnInkSourceSlot I) urnInkNew

abbrev grabSourceEvm2 cA gh bl σ σ₀ A I (g : UInt256)
    (urnInkNew urnArtNew : UInt256) :=
  let evm1 := grabSourceEvm1 cA gh bl σ σ₀ A I g urnInkNew
  Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
    (grabUrnArtSourceSlot I) urnArtNew

abbrev grabSourceEvm3 cA gh bl σ σ₀ A I (g : UInt256)
    (urnInkNew urnArtNew ilkArtNew : UInt256) :=
  let evm2 := grabSourceEvm2 cA gh bl σ σ₀ A I g urnInkNew urnArtNew
  Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
    (grabIlkArtSourceSlot I) ilkArtNew

abbrev grabSourceEvm4 cA gh bl σ σ₀ A I (g : UInt256)
    (urnInkNew urnArtNew ilkArtNew gemNew : UInt256) :=
  let evm3 := grabSourceEvm3 cA gh bl σ σ₀ A I g urnInkNew urnArtNew ilkArtNew
  Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
    (grabGemSourceSlot I) gemNew

abbrev grabSourceEvm5 cA gh bl σ σ₀ A I (g : UInt256)
    (urnInkNew urnArtNew ilkArtNew gemNew sinNew : UInt256) :=
  let evm4 := grabSourceEvm4 cA gh bl σ σ₀ A I g urnInkNew urnArtNew ilkArtNew gemNew
  Solm.EVM.storageStore evm4 evm4.executionEnv.codeOwner
    (grabSinSourceSlot I) sinNew

def grabUrnBase (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨3⟩ (grabIWord I)) (grabUMaskedWord I)

def grabIlkBase (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨2⟩ (grabIWord I)

def grabUrnInkSlot (I : ExecutionEnv) : UInt256 :=
  grabUrnBase I

def grabUrnArtSlot (I : ExecutionEnv) : UInt256 :=
  grabUrnBase I + ⟨1⟩

def grabIlkArtSlot (I : ExecutionEnv) : UInt256 :=
  grabIlkBase I

def grabIlkRateSlot (I : ExecutionEnv) : UInt256 :=
  grabIlkBase I + ⟨1⟩

def grabGemBase (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨4⟩ (grabIWord I)

def grabGemVSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (grabGemBase I) (grabVMaskedWord I)

def grabSinSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨6⟩ (grabWMaskedWord I)

theorem u256_add_one_ne_self (x : UInt256) : x + ⟨1⟩ ≠ x := by
  intro h
  have ht := congrArg UInt256.toNat h
  rw [uadd_toNat] at ht
  have hsumLe : x.toNat + 1 ≤ UInt256.size := by
    have hxlt : x.toNat < UInt256.size := x.val.isLt
    omega
  by_cases hlt : x.toNat + 1 < UInt256.size
  · have hmod : (x.toNat + (⟨1⟩ : UInt256).toNat) % UInt256.size = x.toNat + 1 := by
      rw [show (⟨1⟩ : UInt256).toNat = 1 from by decide]
      exact Nat.mod_eq_of_lt hlt
    rw [hmod] at ht
    omega
  · have hsum : x.toNat + 1 = UInt256.size := by omega
    have hmod : (x.toNat + (⟨1⟩ : UInt256).toNat) % UInt256.size = 0 := by
      rw [show (⟨1⟩ : UInt256).toNat = 1 from by decide, hsum]
      exact Nat.mod_self UInt256.size
    rw [hmod] at ht
    have hsize : 1 < UInt256.size := by native_decide
    omega

theorem grabUrnArtSlot_ne_urnInkSlot (I : ExecutionEnv) :
    grabUrnArtSlot I ≠ grabUrnInkSlot I := by
  simpa [grabUrnArtSlot, grabUrnInkSlot] using u256_add_one_ne_self (grabUrnBase I)

theorem grabIlkRateSlot_ne_ilkArtSlot (I : ExecutionEnv) :
    grabIlkRateSlot I ≠ grabIlkArtSlot I := by
  simpa [grabIlkRateSlot, grabIlkArtSlot] using u256_add_one_ne_self (grabIlkBase I)

theorem vatSlotWord_sstore_ne (σ : AccountMap) (I : ExecutionEnv)
    (readSlot writeSlot val : UInt256) (hne : readSlot ≠ writeSlot) :
    vatSlotWord readSlot (sstoreAccountMap I.codeOwner σ writeSlot val) I =
      vatSlotWord readSlot σ I := by
  exact sstoreAccountMap_storage_findD_ne σ I.codeOwner readSlot writeSlot val hne

theorem solcSlotWord_sstore_ne (σ : AccountMap) (I : ExecutionEnv)
    (readSlot writeSlot val : UInt256) (hne : readSlot ≠ writeSlot) :
    solcSlotWord (sstoreAccountMap I.codeOwner σ writeSlot val) I readSlot =
      solcSlotWord σ I readSlot := by
  simpa [vatSlotWord] using vatSlotWord_sstore_ne σ I readSlot writeSlot val hne

theorem grabUrnArtWord_after_urnInk (σ : AccountMap) (I : ExecutionEnv)
    (urnInkNew : UInt256) :
    vatSlotWord (grabUrnArtSlot I)
        (sstoreAccountMap I.codeOwner σ (grabUrnInkSlot I) urnInkNew) I =
      vatSlotWord (grabUrnArtSlot I) σ I := by
  exact vatSlotWord_sstore_ne σ I (grabUrnArtSlot I) (grabUrnInkSlot I) urnInkNew
    (grabUrnArtSlot_ne_urnInkSlot I)

theorem grabIlkRateWord_after_ilkArt (σ : AccountMap) (I : ExecutionEnv)
    (ilkArtNew : UInt256) :
    vatSlotWord (grabIlkRateSlot I)
        (sstoreAccountMap I.codeOwner σ (grabIlkArtSlot I) ilkArtNew) I =
      vatSlotWord (grabIlkRateSlot I) σ I := by
  exact vatSlotWord_sstore_ne σ I (grabIlkRateSlot I) (grabIlkArtSlot I) ilkArtNew
    (grabIlkRateSlot_ne_ilkArtSlot I)

def grabUrnInkNew (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  grabDinkWord I + solcSlotWord σ I (grabUrnInkSlot I)

def grabAfterUrnInk (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (grabUrnInkSlot I) (grabUrnInkNew σ I)

def grabUrnArtNew (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  grabDartWord I + solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)

theorem grabUrnArtNew_eq_initial (σ : AccountMap) (I : ExecutionEnv) :
    grabUrnArtNew σ I =
      grabDartWord I + solcSlotWord σ I (grabUrnArtSlot I) := by
  have hread :
      solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnInkSlot I) (grabUrnInkNew σ I))
          I (grabUrnArtSlot I) =
        solcSlotWord σ I (grabUrnArtSlot I) := by
    simpa [vatSlotWord] using grabUrnArtWord_after_urnInk σ I (grabUrnInkNew σ I)
  simp [grabUrnArtNew, grabAfterUrnInk, hread]

def grabAfterUrnArt (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (grabAfterUrnInk σ I) (grabUrnArtSlot I)
    (grabUrnArtNew σ I)

def grabIlkArtNew (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  grabDartWord I + solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I)

theorem grabIlkArtWord_after_urnArt_of_ne (σ : AccountMap) (I : ExecutionEnv)
    (hneInk : grabIlkArtSlot I ≠ grabUrnInkSlot I)
    (hneArt : grabIlkArtSlot I ≠ grabUrnArtSlot I) :
    solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I) =
      solcSlotWord σ I (grabIlkArtSlot I) := by
  calc
    solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I) =
        solcSlotWord (grabAfterUrnInk σ I) I (grabIlkArtSlot I) := by
      simpa [grabAfterUrnArt] using
        solcSlotWord_sstore_ne (grabAfterUrnInk σ I) I
          (grabIlkArtSlot I) (grabUrnArtSlot I) (grabUrnArtNew σ I) hneArt
    _ = solcSlotWord σ I (grabIlkArtSlot I) := by
      simpa [grabAfterUrnInk] using
        solcSlotWord_sstore_ne σ I (grabIlkArtSlot I) (grabUrnInkSlot I)
          (grabUrnInkNew σ I) hneInk

theorem grabIlkArtNew_eq_initial_of_ne (σ : AccountMap) (I : ExecutionEnv)
    (hneInk : grabIlkArtSlot I ≠ grabUrnInkSlot I)
    (hneArt : grabIlkArtSlot I ≠ grabUrnArtSlot I) :
    grabIlkArtNew σ I =
      grabDartWord I + solcSlotWord σ I (grabIlkArtSlot I) := by
  simp [grabIlkArtNew, grabIlkArtWord_after_urnArt_of_ne σ I hneInk hneArt]

def grabAfterIlkArt (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (grabAfterUrnArt σ I) (grabIlkArtSlot I)
    (grabIlkArtNew σ I)

def grabDtab (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.mul (grabDartWord I)
    (solcSlotWord (grabAfterIlkArt σ I) I (grabIlkRateSlot I))

theorem grabIlkRateWord_after_ilkArt_of_ne (σ : AccountMap) (I : ExecutionEnv)
    (hneInk : grabIlkRateSlot I ≠ grabUrnInkSlot I)
    (hneArt : grabIlkRateSlot I ≠ grabUrnArtSlot I) :
    solcSlotWord (grabAfterIlkArt σ I) I (grabIlkRateSlot I) =
      solcSlotWord σ I (grabIlkRateSlot I) := by
  calc
    solcSlotWord (grabAfterIlkArt σ I) I (grabIlkRateSlot I) =
        solcSlotWord (grabAfterUrnArt σ I) I (grabIlkRateSlot I) := by
      exact solcSlotWord_sstore_ne (grabAfterUrnArt σ I) I
        (grabIlkRateSlot I) (grabIlkArtSlot I) (grabIlkArtNew σ I)
        (grabIlkRateSlot_ne_ilkArtSlot I)
    _ = solcSlotWord (grabAfterUrnInk σ I) I (grabIlkRateSlot I) := by
      simpa [grabAfterUrnArt] using
        solcSlotWord_sstore_ne (grabAfterUrnInk σ I) I
          (grabIlkRateSlot I) (grabUrnArtSlot I) (grabUrnArtNew σ I) hneArt
    _ = solcSlotWord σ I (grabIlkRateSlot I) := by
      simpa [grabAfterUrnInk] using
        solcSlotWord_sstore_ne σ I (grabIlkRateSlot I) (grabUrnInkSlot I)
          (grabUrnInkNew σ I) hneInk

theorem grabDtab_eq_initial_of_ne (σ : AccountMap) (I : ExecutionEnv)
    (hneInk : grabIlkRateSlot I ≠ grabUrnInkSlot I)
    (hneArt : grabIlkRateSlot I ≠ grabUrnArtSlot I) :
    grabDtab σ I =
      UInt256.mul (grabDartWord I) (solcSlotWord σ I (grabIlkRateSlot I)) := by
  simp [grabDtab, grabIlkRateWord_after_ilkArt_of_ne σ I hneInk hneArt]

theorem grabIlkRateWord_after_ilkArt_store (σ : AccountMap) (I : ExecutionEnv)
    (ilkArtNew : UInt256) :
    solcSlotWord (sstoreAccountMap I.codeOwner σ (grabIlkArtSlot I) ilkArtNew)
        I (grabIlkRateSlot I) =
      solcSlotWord σ I (grabIlkRateSlot I) := by
  simpa [vatSlotWord] using grabIlkRateWord_after_ilkArt σ I ilkArtNew

def grabGemNew (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub (solcSlotWord (grabAfterIlkArt σ I) I (grabGemVSlot I)) (grabDinkWord I)

theorem grabGemWord_after_ilkArt_of_ne (σ : AccountMap) (I : ExecutionEnv)
    (hneInk : grabGemVSlot I ≠ grabUrnInkSlot I)
    (hneArt : grabGemVSlot I ≠ grabUrnArtSlot I)
    (hneIlk : grabGemVSlot I ≠ grabIlkArtSlot I) :
    solcSlotWord (grabAfterIlkArt σ I) I (grabGemVSlot I) =
      solcSlotWord σ I (grabGemVSlot I) := by
  calc
    solcSlotWord (grabAfterIlkArt σ I) I (grabGemVSlot I) =
        solcSlotWord (grabAfterUrnArt σ I) I (grabGemVSlot I) := by
      exact solcSlotWord_sstore_ne (grabAfterUrnArt σ I) I
        (grabGemVSlot I) (grabIlkArtSlot I) (grabIlkArtNew σ I) hneIlk
    _ = solcSlotWord (grabAfterUrnInk σ I) I (grabGemVSlot I) := by
      simpa [grabAfterUrnArt] using
        solcSlotWord_sstore_ne (grabAfterUrnInk σ I) I
          (grabGemVSlot I) (grabUrnArtSlot I) (grabUrnArtNew σ I) hneArt
    _ = solcSlotWord σ I (grabGemVSlot I) := by
      simpa [grabAfterUrnInk] using
        solcSlotWord_sstore_ne σ I (grabGemVSlot I) (grabUrnInkSlot I)
          (grabUrnInkNew σ I) hneInk

theorem grabGemNew_eq_initial_of_ne (σ : AccountMap) (I : ExecutionEnv)
    (hneInk : grabGemVSlot I ≠ grabUrnInkSlot I)
    (hneArt : grabGemVSlot I ≠ grabUrnArtSlot I)
    (hneIlk : grabGemVSlot I ≠ grabIlkArtSlot I) :
    grabGemNew σ I =
      UInt256.sub (solcSlotWord σ I (grabGemVSlot I)) (grabDinkWord I) := by
  simp [grabGemNew, grabGemWord_after_ilkArt_of_ne σ I hneInk hneArt hneIlk]

def grabAfterGem (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (grabAfterIlkArt σ I) (grabGemVSlot I) (grabGemNew σ I)

def grabSinNew (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub (solcSlotWord (grabAfterGem σ I) I (grabSinSlot I)) (grabDtab σ I)

theorem grabSinWord_after_gem_of_ne (σ : AccountMap) (I : ExecutionEnv)
    (hneInk : grabSinSlot I ≠ grabUrnInkSlot I)
    (hneArt : grabSinSlot I ≠ grabUrnArtSlot I)
    (hneIlk : grabSinSlot I ≠ grabIlkArtSlot I)
    (hneGem : grabSinSlot I ≠ grabGemVSlot I) :
    solcSlotWord (grabAfterGem σ I) I (grabSinSlot I) =
      solcSlotWord σ I (grabSinSlot I) := by
  calc
    solcSlotWord (grabAfterGem σ I) I (grabSinSlot I) =
        solcSlotWord (grabAfterIlkArt σ I) I (grabSinSlot I) := by
      exact solcSlotWord_sstore_ne (grabAfterIlkArt σ I) I
        (grabSinSlot I) (grabGemVSlot I) (grabGemNew σ I) hneGem
    _ = solcSlotWord (grabAfterUrnArt σ I) I (grabSinSlot I) := by
      simpa [grabAfterIlkArt] using
        solcSlotWord_sstore_ne (grabAfterUrnArt σ I) I
          (grabSinSlot I) (grabIlkArtSlot I) (grabIlkArtNew σ I) hneIlk
    _ = solcSlotWord (grabAfterUrnInk σ I) I (grabSinSlot I) := by
      simpa [grabAfterUrnArt] using
        solcSlotWord_sstore_ne (grabAfterUrnInk σ I) I
          (grabSinSlot I) (grabUrnArtSlot I) (grabUrnArtNew σ I) hneArt
    _ = solcSlotWord σ I (grabSinSlot I) := by
      simpa [grabAfterUrnInk] using
        solcSlotWord_sstore_ne σ I (grabSinSlot I) (grabUrnInkSlot I)
          (grabUrnInkNew σ I) hneInk

theorem grabSinNew_eq_initial_of_ne (σ : AccountMap) (I : ExecutionEnv)
    (dtabWord : UInt256)
    (hneInk : grabSinSlot I ≠ grabUrnInkSlot I)
    (hneArt : grabSinSlot I ≠ grabUrnArtSlot I)
    (hneIlk : grabSinSlot I ≠ grabIlkArtSlot I)
    (hneGem : grabSinSlot I ≠ grabGemVSlot I)
    (hDtabWord : dtabWord = grabDtab σ I) :
    grabSinNew σ I =
      UInt256.sub (solcSlotWord σ I (grabSinSlot I)) dtabWord := by
  simp [grabSinNew, grabSinWord_after_gem_of_ne σ I hneInk hneArt hneIlk hneGem,
    hDtabWord]

def grabAfterSin (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (grabAfterGem σ I) (grabSinSlot I) (grabSinNew σ I)

def grabViceNew (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub (solcSlotWord (grabAfterSin σ I) I ⟨8⟩) (grabDtab σ I)

theorem grabViceWord_after_sin_of_ne (σ : AccountMap) (I : ExecutionEnv)
    (hneInk : (⟨8⟩ : UInt256) ≠ grabUrnInkSlot I)
    (hneArt : (⟨8⟩ : UInt256) ≠ grabUrnArtSlot I)
    (hneIlk : (⟨8⟩ : UInt256) ≠ grabIlkArtSlot I)
    (hneGem : (⟨8⟩ : UInt256) ≠ grabGemVSlot I)
    (hneSin : (⟨8⟩ : UInt256) ≠ grabSinSlot I) :
    solcSlotWord (grabAfterSin σ I) I ⟨8⟩ =
      solcSlotWord σ I ⟨8⟩ := by
  calc
    solcSlotWord (grabAfterSin σ I) I ⟨8⟩ =
        solcSlotWord (grabAfterGem σ I) I ⟨8⟩ := by
      exact solcSlotWord_sstore_ne (grabAfterGem σ I) I
        ⟨8⟩ (grabSinSlot I) (grabSinNew σ I) hneSin
    _ = solcSlotWord (grabAfterIlkArt σ I) I ⟨8⟩ := by
      simpa [grabAfterGem] using
        solcSlotWord_sstore_ne (grabAfterIlkArt σ I) I
          ⟨8⟩ (grabGemVSlot I) (grabGemNew σ I) hneGem
    _ = solcSlotWord (grabAfterUrnArt σ I) I ⟨8⟩ := by
      simpa [grabAfterIlkArt] using
        solcSlotWord_sstore_ne (grabAfterUrnArt σ I) I
          ⟨8⟩ (grabIlkArtSlot I) (grabIlkArtNew σ I) hneIlk
    _ = solcSlotWord (grabAfterUrnInk σ I) I ⟨8⟩ := by
      simpa [grabAfterUrnArt] using
        solcSlotWord_sstore_ne (grabAfterUrnInk σ I) I
          ⟨8⟩ (grabUrnArtSlot I) (grabUrnArtNew σ I) hneArt
    _ = solcSlotWord σ I ⟨8⟩ := by
      simpa [grabAfterUrnInk] using
        solcSlotWord_sstore_ne σ I ⟨8⟩ (grabUrnInkSlot I)
          (grabUrnInkNew σ I) hneInk

theorem grabViceNew_eq_initial_of_ne (σ : AccountMap) (I : ExecutionEnv)
    (dtabWord : UInt256)
    (hneInk : (⟨8⟩ : UInt256) ≠ grabUrnInkSlot I)
    (hneArt : (⟨8⟩ : UInt256) ≠ grabUrnArtSlot I)
    (hneIlk : (⟨8⟩ : UInt256) ≠ grabIlkArtSlot I)
    (hneGem : (⟨8⟩ : UInt256) ≠ grabGemVSlot I)
    (hneSin : (⟨8⟩ : UInt256) ≠ grabSinSlot I)
    (hDtabWord : dtabWord = grabDtab σ I) :
    grabViceNew σ I =
      UInt256.sub (solcSlotWord σ I ⟨8⟩) dtabWord := by
  simp [grabViceNew, grabViceWord_after_sin_of_ne σ I hneInk hneArt hneIlk hneGem hneSin,
    hDtabWord]

def grabAfterVice (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (grabAfterSin σ I) ⟨8⟩ (grabViceNew σ I)

def grabInkNegOk (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  UInt256.slt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt (grabUrnInkNew σ I) (solcSlotWord σ I (grabUrnInkSlot I)) = ⟨0⟩

def grabInkPosOk (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  UInt256.sgt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt (grabUrnInkNew σ I) (solcSlotWord σ I (grabUrnInkSlot I)) = ⟨0⟩

def grabUrnArtNegOk (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  UInt256.slt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt (grabUrnArtNew σ I)
      (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)) = ⟨0⟩

def grabUrnArtPosOk (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  UInt256.sgt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt (grabUrnArtNew σ I)
      (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)) = ⟨0⟩

def grabIlkArtNegOk (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  UInt256.slt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt (grabIlkArtNew σ I)
      (solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I)) = ⟨0⟩

def grabIlkArtPosOk (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  UInt256.sgt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt (grabIlkArtNew σ I)
      (solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I)) = ⟨0⟩

def grabDtabMaxOk (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  UInt256.slt (solcSlotWord (grabAfterIlkArt σ I) I (grabIlkRateSlot I)) ⟨0⟩ = ⟨0⟩

def grabDtabMulOk (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  grabDartWord I = ⟨0⟩ ∨
    UInt256.eq
      (UInt256.sdiv
        (UInt256.mul (grabDartWord I)
          (solcSlotWord (grabAfterIlkArt σ I) I (grabIlkRateSlot I)))
        (grabDartWord I))
      (solcSlotWord (grabAfterIlkArt σ I) I (grabIlkRateSlot I)) ≠ ⟨0⟩

def grabGemPosOk (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  UInt256.sgt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt (grabGemNew σ I)
      (solcSlotWord (grabAfterIlkArt σ I) I (grabGemVSlot I)) = ⟨0⟩

def grabGemNegOk (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  UInt256.slt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt (grabGemNew σ I)
      (solcSlotWord (grabAfterIlkArt σ I) I (grabGemVSlot I)) = ⟨0⟩

def grabSinPosOk (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  UInt256.sgt (grabDtab σ I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt (grabSinNew σ I)
      (solcSlotWord (grabAfterGem σ I) I (grabSinSlot I)) = ⟨0⟩

def grabSinNegOk (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  UInt256.slt (grabDtab σ I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt (grabSinNew σ I)
      (solcSlotWord (grabAfterGem σ I) I (grabSinSlot I)) = ⟨0⟩

def grabVicePosOk (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  UInt256.sgt (grabDtab σ I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.gt (grabViceNew σ I)
      (solcSlotWord (grabAfterSin σ I) I ⟨8⟩) = ⟨0⟩

def grabViceNegOk (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  UInt256.slt (grabDtab σ I) ⟨0⟩ = ⟨0⟩ ∨
    UInt256.lt (grabViceNew σ I)
      (solcSlotWord (grabAfterSin σ I) I ⟨8⟩) = ⟨0⟩

theorem accountMapEquiv_grabAfterVice {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    accountMapEquiv (grabAfterVice σ I) (grabAfterVice τ I) := by
  have hInkOld :
      solcSlotWord σ I (grabUrnInkSlot I) =
        solcSlotWord τ I (grabUrnInkSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (grabUrnInkSlot I) ⟨0⟩
  have hInkNew : grabUrnInkNew σ I = grabUrnInkNew τ I := by
    simp [grabUrnInkNew, hInkOld]
  have hInk :
      accountMapEquiv (grabAfterUrnInk σ I) (grabAfterUrnInk τ I) := by
    simp [grabAfterUrnInk, hInkNew,
      accountMapEquiv_sstoreAccountMap I.codeOwner (grabUrnInkSlot I)
        (grabUrnInkNew τ I) hAccounts]
  have hArtOld :
      solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I) =
        solcSlotWord (grabAfterUrnInk τ I) I (grabUrnArtSlot I) :=
    accountMapEquiv_storage_findD hInk I.codeOwner (grabUrnArtSlot I) ⟨0⟩
  have hArtNew : grabUrnArtNew σ I = grabUrnArtNew τ I := by
    simp [grabUrnArtNew, hArtOld]
  have hArt :
      accountMapEquiv (grabAfterUrnArt σ I) (grabAfterUrnArt τ I) := by
    simp [grabAfterUrnArt, hArtNew,
      accountMapEquiv_sstoreAccountMap I.codeOwner (grabUrnArtSlot I)
        (grabUrnArtNew τ I) hInk]
  have hIlkArtOld :
      solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I) =
        solcSlotWord (grabAfterUrnArt τ I) I (grabIlkArtSlot I) :=
    accountMapEquiv_storage_findD hArt I.codeOwner (grabIlkArtSlot I) ⟨0⟩
  have hIlkArtNew : grabIlkArtNew σ I = grabIlkArtNew τ I := by
    simp [grabIlkArtNew, hIlkArtOld]
  have hIlk :
      accountMapEquiv (grabAfterIlkArt σ I) (grabAfterIlkArt τ I) := by
    simp [grabAfterIlkArt, hIlkArtNew,
      accountMapEquiv_sstoreAccountMap I.codeOwner (grabIlkArtSlot I)
        (grabIlkArtNew τ I) hArt]
  have hRate :
      solcSlotWord (grabAfterIlkArt σ I) I (grabIlkRateSlot I) =
        solcSlotWord (grabAfterIlkArt τ I) I (grabIlkRateSlot I) :=
    accountMapEquiv_storage_findD hIlk I.codeOwner (grabIlkRateSlot I) ⟨0⟩
  have hDtab : grabDtab σ I = grabDtab τ I := by
    simp [grabDtab, hRate]
  have hGemOld :
      solcSlotWord (grabAfterIlkArt σ I) I (grabGemVSlot I) =
        solcSlotWord (grabAfterIlkArt τ I) I (grabGemVSlot I) :=
    accountMapEquiv_storage_findD hIlk I.codeOwner (grabGemVSlot I) ⟨0⟩
  have hGemNew : grabGemNew σ I = grabGemNew τ I := by
    simp [grabGemNew, hGemOld]
  have hGem :
      accountMapEquiv (grabAfterGem σ I) (grabAfterGem τ I) := by
    simp [grabAfterGem, hGemNew,
      accountMapEquiv_sstoreAccountMap I.codeOwner (grabGemVSlot I)
        (grabGemNew τ I) hIlk]
  have hSinOld :
      solcSlotWord (grabAfterGem σ I) I (grabSinSlot I) =
        solcSlotWord (grabAfterGem τ I) I (grabSinSlot I) :=
    accountMapEquiv_storage_findD hGem I.codeOwner (grabSinSlot I) ⟨0⟩
  have hSinNew : grabSinNew σ I = grabSinNew τ I := by
    simp [grabSinNew, hSinOld, hDtab]
  have hSin :
      accountMapEquiv (grabAfterSin σ I) (grabAfterSin τ I) := by
    simp [grabAfterSin, hSinNew,
      accountMapEquiv_sstoreAccountMap I.codeOwner (grabSinSlot I)
        (grabSinNew τ I) hGem]
  have hViceOld :
      solcSlotWord (grabAfterSin σ I) I ⟨8⟩ =
        solcSlotWord (grabAfterSin τ I) I ⟨8⟩ :=
    accountMapEquiv_storage_findD hSin I.codeOwner ⟨8⟩ ⟨0⟩
  have hViceNew : grabViceNew σ I = grabViceNew τ I := by
    simp [grabViceNew, hViceOld, hDtab]
  simp [grabAfterVice, hViceNew,
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨8⟩ (grabViceNew τ I) hSin]

theorem accountMapEquiv_grabGuards
    {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hInkNeg : grabInkNegOk σ I) (hInkPos : grabInkPosOk σ I)
    (hUrnArtNeg : grabUrnArtNegOk σ I) (hUrnArtPos : grabUrnArtPosOk σ I)
    (hIlkArtNeg : grabIlkArtNegOk σ I) (hIlkArtPos : grabIlkArtPosOk σ I)
    (hDtabMax : grabDtabMaxOk σ I) (hDtabMul : grabDtabMulOk σ I)
    (hGemPos : grabGemPosOk σ I) (hGemNeg : grabGemNegOk σ I)
    (hSinPos : grabSinPosOk σ I) (hSinNeg : grabSinNegOk σ I)
    (hVicePos : grabVicePosOk σ I) (hViceNeg : grabViceNegOk σ I) :
    grabInkNegOk τ I ∧ grabInkPosOk τ I ∧
    grabUrnArtNegOk τ I ∧ grabUrnArtPosOk τ I ∧
    grabIlkArtNegOk τ I ∧ grabIlkArtPosOk τ I ∧
    grabDtabMaxOk τ I ∧ grabDtabMulOk τ I ∧
    grabGemPosOk τ I ∧ grabGemNegOk τ I ∧
    grabSinPosOk τ I ∧ grabSinNegOk τ I ∧
    grabVicePosOk τ I ∧ grabViceNegOk τ I := by
  have hInkOld :
      solcSlotWord σ I (grabUrnInkSlot I) =
        solcSlotWord τ I (grabUrnInkSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (grabUrnInkSlot I) ⟨0⟩
  have hInkNew : grabUrnInkNew σ I = grabUrnInkNew τ I := by
    simp [grabUrnInkNew, hInkOld]
  have hInk :
      accountMapEquiv (grabAfterUrnInk σ I) (grabAfterUrnInk τ I) := by
    simp [grabAfterUrnInk, hInkNew,
      accountMapEquiv_sstoreAccountMap I.codeOwner (grabUrnInkSlot I)
        (grabUrnInkNew τ I) hAccounts]
  have hArtOld :
      solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I) =
        solcSlotWord (grabAfterUrnInk τ I) I (grabUrnArtSlot I) :=
    accountMapEquiv_storage_findD hInk I.codeOwner (grabUrnArtSlot I) ⟨0⟩
  have hArtNew : grabUrnArtNew σ I = grabUrnArtNew τ I := by
    simp [grabUrnArtNew, hArtOld]
  have hArt :
      accountMapEquiv (grabAfterUrnArt σ I) (grabAfterUrnArt τ I) := by
    simp [grabAfterUrnArt, hArtNew,
      accountMapEquiv_sstoreAccountMap I.codeOwner (grabUrnArtSlot I)
        (grabUrnArtNew τ I) hInk]
  have hIlkArtOld :
      solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I) =
        solcSlotWord (grabAfterUrnArt τ I) I (grabIlkArtSlot I) :=
    accountMapEquiv_storage_findD hArt I.codeOwner (grabIlkArtSlot I) ⟨0⟩
  have hIlkArtNew : grabIlkArtNew σ I = grabIlkArtNew τ I := by
    simp [grabIlkArtNew, hIlkArtOld]
  have hIlk :
      accountMapEquiv (grabAfterIlkArt σ I) (grabAfterIlkArt τ I) := by
    simp [grabAfterIlkArt, hIlkArtNew,
      accountMapEquiv_sstoreAccountMap I.codeOwner (grabIlkArtSlot I)
        (grabIlkArtNew τ I) hArt]
  have hRate :
      solcSlotWord (grabAfterIlkArt σ I) I (grabIlkRateSlot I) =
        solcSlotWord (grabAfterIlkArt τ I) I (grabIlkRateSlot I) :=
    accountMapEquiv_storage_findD hIlk I.codeOwner (grabIlkRateSlot I) ⟨0⟩
  have hDtab : grabDtab σ I = grabDtab τ I := by
    simp [grabDtab, hRate]
  have hGemOld :
      solcSlotWord (grabAfterIlkArt σ I) I (grabGemVSlot I) =
        solcSlotWord (grabAfterIlkArt τ I) I (grabGemVSlot I) :=
    accountMapEquiv_storage_findD hIlk I.codeOwner (grabGemVSlot I) ⟨0⟩
  have hGemNew : grabGemNew σ I = grabGemNew τ I := by
    simp [grabGemNew, hGemOld]
  have hGem :
      accountMapEquiv (grabAfterGem σ I) (grabAfterGem τ I) := by
    simp [grabAfterGem, hGemNew,
      accountMapEquiv_sstoreAccountMap I.codeOwner (grabGemVSlot I)
        (grabGemNew τ I) hIlk]
  have hSinOld :
      solcSlotWord (grabAfterGem σ I) I (grabSinSlot I) =
        solcSlotWord (grabAfterGem τ I) I (grabSinSlot I) :=
    accountMapEquiv_storage_findD hGem I.codeOwner (grabSinSlot I) ⟨0⟩
  have hSinNew : grabSinNew σ I = grabSinNew τ I := by
    simp [grabSinNew, hSinOld, hDtab]
  have hSin :
      accountMapEquiv (grabAfterSin σ I) (grabAfterSin τ I) := by
    simp [grabAfterSin, hSinNew,
      accountMapEquiv_sstoreAccountMap I.codeOwner (grabSinSlot I)
        (grabSinNew τ I) hGem]
  have hViceOld :
      solcSlotWord (grabAfterSin σ I) I ⟨8⟩ =
        solcSlotWord (grabAfterSin τ I) I ⟨8⟩ :=
    accountMapEquiv_storage_findD hSin I.codeOwner ⟨8⟩ ⟨0⟩
  have hViceNew : grabViceNew σ I = grabViceNew τ I := by
    simp [grabViceNew, hViceOld, hDtab]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [grabInkNegOk, hInkOld, hInkNew] using hInkNeg
  · simpa [grabInkPosOk, hInkOld, hInkNew] using hInkPos
  · simpa [grabUrnArtNegOk, hArtOld, hArtNew] using hUrnArtNeg
  · simpa [grabUrnArtPosOk, hArtOld, hArtNew] using hUrnArtPos
  · simpa [grabIlkArtNegOk, hIlkArtOld, hIlkArtNew] using hIlkArtNeg
  · simpa [grabIlkArtPosOk, hIlkArtOld, hIlkArtNew] using hIlkArtPos
  · simpa [grabDtabMaxOk, hRate] using hDtabMax
  · simpa [grabDtabMulOk, hRate] using hDtabMul
  · simpa [grabGemPosOk, hGemOld, hGemNew] using hGemPos
  · simpa [grabGemNegOk, hGemOld, hGemNew] using hGemNeg
  · simpa [grabSinPosOk, hDtab, hSinOld, hSinNew] using hSinPos
  · simpa [grabSinNegOk, hDtab, hSinOld, hSinNew] using hSinNeg
  · simpa [grabVicePosOk, hDtab, hViceOld, hViceNew] using hVicePos
  · simpa [grabViceNegOk, hDtab, hViceOld, hViceNew] using hViceNeg

theorem accountMapEquiv_grabAddGuards
    {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hInkNeg : grabInkNegOk σ I) (hInkPos : grabInkPosOk σ I)
    (hUrnArtNeg : grabUrnArtNegOk σ I) (hUrnArtPos : grabUrnArtPosOk σ I)
    (hIlkArtNeg : grabIlkArtNegOk σ I) (hIlkArtPos : grabIlkArtPosOk σ I) :
    grabInkNegOk τ I ∧ grabInkPosOk τ I ∧
    grabUrnArtNegOk τ I ∧ grabUrnArtPosOk τ I ∧
    grabIlkArtNegOk τ I ∧ grabIlkArtPosOk τ I ∧
    accountMapEquiv (grabAfterIlkArt σ I) (grabAfterIlkArt τ I) := by
  have hInkOld :
      solcSlotWord σ I (grabUrnInkSlot I) =
        solcSlotWord τ I (grabUrnInkSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (grabUrnInkSlot I) ⟨0⟩
  have hInkNew : grabUrnInkNew σ I = grabUrnInkNew τ I := by
    simp [grabUrnInkNew, hInkOld]
  have hInk :
      accountMapEquiv (grabAfterUrnInk σ I) (grabAfterUrnInk τ I) := by
    simp [grabAfterUrnInk, hInkNew,
      accountMapEquiv_sstoreAccountMap I.codeOwner (grabUrnInkSlot I)
        (grabUrnInkNew τ I) hAccounts]
  have hArtOld :
      solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I) =
        solcSlotWord (grabAfterUrnInk τ I) I (grabUrnArtSlot I) :=
    accountMapEquiv_storage_findD hInk I.codeOwner (grabUrnArtSlot I) ⟨0⟩
  have hArtNew : grabUrnArtNew σ I = grabUrnArtNew τ I := by
    simp [grabUrnArtNew, hArtOld]
  have hArt :
      accountMapEquiv (grabAfterUrnArt σ I) (grabAfterUrnArt τ I) := by
    simp [grabAfterUrnArt, hArtNew,
      accountMapEquiv_sstoreAccountMap I.codeOwner (grabUrnArtSlot I)
        (grabUrnArtNew τ I) hInk]
  have hIlkArtOld :
      solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I) =
        solcSlotWord (grabAfterUrnArt τ I) I (grabIlkArtSlot I) :=
    accountMapEquiv_storage_findD hArt I.codeOwner (grabIlkArtSlot I) ⟨0⟩
  have hIlkArtNew : grabIlkArtNew σ I = grabIlkArtNew τ I := by
    simp [grabIlkArtNew, hIlkArtOld]
  have hIlk :
      accountMapEquiv (grabAfterIlkArt σ I) (grabAfterIlkArt τ I) := by
    simp [grabAfterIlkArt, hIlkArtNew,
      accountMapEquiv_sstoreAccountMap I.codeOwner (grabIlkArtSlot I)
        (grabIlkArtNew τ I) hArt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hIlk⟩
  · simpa [grabInkNegOk, hInkOld, hInkNew] using hInkNeg
  · simpa [grabInkPosOk, hInkOld, hInkNew] using hInkPos
  · simpa [grabUrnArtNegOk, hArtOld, hArtNew] using hUrnArtNeg
  · simpa [grabUrnArtPosOk, hArtOld, hArtNew] using hUrnArtPos
  · simpa [grabIlkArtNegOk, hIlkArtOld, hIlkArtNew] using hIlkArtNeg
  · simpa [grabIlkArtPosOk, hIlkArtOld, hIlkArtNew] using hIlkArtPos

theorem accountMapEquiv_grabSourceGuardConds
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hIlkArtRead :
      solcSlotWord (grabAfterUrnArt σ_solm I) I (grabIlkArtSlot I) =
        vatSlotWord (grabIlkArtSlot I) σ_solm I)
    (hGemRead :
      solcSlotWord (grabAfterIlkArt σ_solm I) I (grabGemVSlot I) =
        vatSlotWord (grabGemVSlot I) σ_solm I)
    (hSinRead :
      solcSlotWord (grabAfterGem σ_solm I) I (grabSinSlot I) =
        vatSlotWord (grabSinSlot I) σ_solm I)
    (hViceRead :
      solcSlotWord (grabAfterSin σ_solm I) I ⟨8⟩ =
        vatSlotWord ⟨8⟩ σ_solm I)
    (dtab : Int) (dtabWord : UInt256)
    (hDtabWord : dtabWord = grabDtab σ_solm I)
    (hdtabLo : -((2 : Int) ^ 255) ≤ dtab)
    (hdtabHi : dtab < (2 : Int) ^ 255)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hInkNeg : grabInkNegOk σ_evm I) (hInkPos : grabInkPosOk σ_evm I)
    (hUrnArtNeg : grabUrnArtNegOk σ_evm I)
    (hUrnArtPos : grabUrnArtPosOk σ_evm I)
    (hIlkArtNeg : grabIlkArtNegOk σ_evm I)
    (hIlkArtPos : grabIlkArtPosOk σ_evm I)
    (hDtabMax : grabDtabMaxOk σ_evm I) (hDtabMul : grabDtabMulOk σ_evm I)
    (hGemPos : grabGemPosOk σ_evm I) (hGemNeg : grabGemNegOk σ_evm I)
    (hSinPos : grabSinPosOk σ_evm I) (hSinNeg : grabSinNegOk σ_evm I)
    (hVicePos : grabVicePosOk σ_evm I) (hViceNeg : grabViceNegOk σ_evm I) :
    (0 ≤ grabDinkInt I ∨
      (grabUrnInkNew σ_solm I).toNat ≤
        (vatSlotWord (grabUrnInkSlot I) σ_solm I).toNat) ∧
    (grabDinkInt I ≤ 0 ∨
      (vatSlotWord (grabUrnInkSlot I) σ_solm I).toNat ≤
        (grabUrnInkNew σ_solm I).toNat) ∧
    (0 ≤ grabDartInt I ∨
      (grabUrnArtNew σ_solm I).toNat ≤
        (vatSlotWord (grabUrnArtSlot I) σ_solm I).toNat) ∧
    (grabDartInt I ≤ 0 ∨
      (vatSlotWord (grabUrnArtSlot I) σ_solm I).toNat ≤
        (grabUrnArtNew σ_solm I).toNat) ∧
    (0 ≤ grabDartInt I ∨
      (grabIlkArtNew σ_solm I).toNat ≤
        (vatSlotWord (grabIlkArtSlot I) σ_solm I).toNat) ∧
    (grabDartInt I ≤ 0 ∨
      (vatSlotWord (grabIlkArtSlot I) σ_solm I).toNat ≤
        (grabIlkArtNew σ_solm I).toNat) ∧
    (grabDinkInt I ≤ 0 ∨
      (grabGemNew σ_solm I).toNat ≤
        (vatSlotWord (grabGemVSlot I) σ_solm I).toNat) ∧
    (0 ≤ grabDinkInt I ∨
      (vatSlotWord (grabGemVSlot I) σ_solm I).toNat ≤
        (grabGemNew σ_solm I).toNat) ∧
    (dtab ≤ 0 ∨
      (grabSinNew σ_solm I).toNat ≤
        (vatSlotWord (grabSinSlot I) σ_solm I).toNat) ∧
    (0 ≤ dtab ∨
      (vatSlotWord (grabSinSlot I) σ_solm I).toNat ≤
        (grabSinNew σ_solm I).toNat) ∧
    (dtab ≤ 0 ∨
      (grabViceNew σ_solm I).toNat ≤ (vatSlotWord ⟨8⟩ σ_solm I).toNat) ∧
    (0 ≤ dtab ∨
      (vatSlotWord ⟨8⟩ σ_solm I).toNat ≤ (grabViceNew σ_solm I).toNat) := by
  rcases accountMapEquiv_grabGuards hAccounts hInkNeg hInkPos hUrnArtNeg
      hUrnArtPos hIlkArtNeg hIlkArtPos hDtabMax hDtabMul hGemPos hGemNeg hSinPos
      hSinNeg hVicePos hViceNeg with
    ⟨hInkNegS, hInkPosS, hUrnArtNegS, hUrnArtPosS, hIlkArtNegS,
      hIlkArtPosS, _, _, hGemPosS, hGemNegS, hSinPosS, hSinNegS, hVicePosS,
      hViceNegS⟩
  have hUrnArtRead :
      solcSlotWord (grabAfterUrnInk σ_solm I) I (grabUrnArtSlot I) =
        vatSlotWord (grabUrnArtSlot I) σ_solm I := by
    simpa [grabAfterUrnInk, vatSlotWord] using
      grabUrnArtWord_after_urnInk σ_solm I (grabUrnInkNew σ_solm I)
  have hUrnArtNegInit :
      UInt256.slt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (grabUrnArtNew σ_solm I)
          (vatSlotWord (grabUrnArtSlot I) σ_solm I) = ⟨0⟩ := by
    simpa [grabUrnArtNegOk, hUrnArtRead] using hUrnArtNegS
  have hUrnArtPosInit :
      UInt256.sgt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (grabUrnArtNew σ_solm I)
          (vatSlotWord (grabUrnArtSlot I) σ_solm I) = ⟨0⟩ := by
    simpa [grabUrnArtPosOk, hUrnArtRead] using hUrnArtPosS
  have hIlkArtNegInit :
      UInt256.slt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (grabIlkArtNew σ_solm I)
          (vatSlotWord (grabIlkArtSlot I) σ_solm I) = ⟨0⟩ := by
    simpa [grabIlkArtNegOk, hIlkArtRead] using hIlkArtNegS
  have hIlkArtPosInit :
      UInt256.sgt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (grabIlkArtNew σ_solm I)
          (vatSlotWord (grabIlkArtSlot I) σ_solm I) = ⟨0⟩ := by
    simpa [grabIlkArtPosOk, hIlkArtRead] using hIlkArtPosS
  have hGemPosInit :
      UInt256.sgt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (grabGemNew σ_solm I)
          (vatSlotWord (grabGemVSlot I) σ_solm I) = ⟨0⟩ := by
    simpa [grabGemPosOk, hGemRead] using hGemPosS
  have hGemNegInit :
      UInt256.slt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (grabGemNew σ_solm I)
          (vatSlotWord (grabGemVSlot I) σ_solm I) = ⟨0⟩ := by
    simpa [grabGemNegOk, hGemRead] using hGemNegS
  have hSinPosInit :
      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (grabSinNew σ_solm I)
          (vatSlotWord (grabSinSlot I) σ_solm I) = ⟨0⟩ := by
    simpa [grabSinPosOk, hSinRead, hDtabWord] using hSinPosS
  have hSinNegInit :
      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (grabSinNew σ_solm I)
          (vatSlotWord (grabSinSlot I) σ_solm I) = ⟨0⟩ := by
    simpa [grabSinNegOk, hSinRead, hDtabWord] using hSinNegS
  have hVicePosInit :
      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (grabViceNew σ_solm I) (vatSlotWord ⟨8⟩ σ_solm I) = ⟨0⟩ := by
    simpa [grabVicePosOk, hViceRead, hDtabWord] using hVicePosS
  have hViceNegInit :
      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (grabViceNew σ_solm I) (vatSlotWord ⟨8⟩ σ_solm I) = ⟨0⟩ := by
    simpa [grabViceNegOk, hViceRead, hDtabWord] using hViceNegS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact grabDinkAddGuardNegCond hInkNegS
  · exact grabDinkAddGuardPosCond hInkPosS
  · exact grabDartAddGuardNegCond hUrnArtNegInit
  · exact grabDartAddGuardPosCond hUrnArtPosInit
  · exact grabDartAddGuardNegCond hIlkArtNegInit
  · exact grabDartAddGuardPosCond hIlkArtPosInit
  · exact grabDinkSubGuardNegCond hGemPosInit
  · exact grabDinkSubGuardPosCond hGemNegInit
  · exact grabDtabSubGuardNegCond hdtabLo hdtabHi hdtabMod hSinPosInit
  · exact grabDtabSubGuardPosCond hdtabLo hdtabHi hdtabMod hSinNegInit
  · exact grabDtabSubGuardNegCond hdtabLo hdtabHi hdtabMod hVicePosInit
  · exact grabDtabSubGuardPosCond hdtabLo hdtabHi hdtabMod hViceNegInit

theorem grabUMaskedWord_clean (I : ExecutionEnv) :
    UInt256.land (grabUMaskedWord I) solcAddrMask = grabUMaskedWord I := by
  unfold grabUMaskedWord
  rw [u256_land_comm solcAddrMask (grabUWord I)]
  exact solcAddrMask_clean (solcAddrMask_result_canonical (grabUWord I))

theorem grabVMaskedWord_clean (I : ExecutionEnv) :
    UInt256.land (grabVMaskedWord I) solcAddrMask = grabVMaskedWord I := by
  unfold grabVMaskedWord
  rw [u256_land_comm solcAddrMask (grabVWord I)]
  exact solcAddrMask_clean (solcAddrMask_result_canonical (grabVWord I))

theorem grabWMaskedWord_clean (I : ExecutionEnv) :
    UInt256.land (grabWMaskedWord I) solcAddrMask = grabWMaskedWord I := by
  unfold grabWMaskedWord
  rw [u256_land_comm solcAddrMask (grabWWord I)]
  exact solcAddrMask_clean (solcAddrMask_result_canonical (grabWWord I))

private theorem grabIBytes_len (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    ((I.calldata.toList.drop 4).take 32).length = ↑bytes32Width + 1 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [List.length_take, List.length_drop, htlen]
  simp [bytes32Width]
  omega

theorem grabIKeyWord_eq (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (grabIKey I) = grabIWord I := by
  have hword : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      uInt256OfByteArray (I.calldata.readBytes 4 32) :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  simp [keyValueToWord, bytes32Width, ABI.bytesToWord, fromByteArrayBigEndian,
    byteArray_toList_eq, show 32 ≤ I.calldata.size - 4 by omega] at hword ⊢
  exact hword

theorem grabUrnSourceBase_eq (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    grabUrnSourceBase I = grabUrnBase I := by
  unfold grabUrnSourceBase grabUrnBase urnsBase urnsIlkSlot grabIKey grabUKey
    grabUMaskedWord mapSlot solcMappingSlot
  rw [grabIKeyWord_eq I (by omega), keyValueToWord_address_ofNat_mask]

theorem grabUrnInkSourceSlot_eq (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    grabUrnInkSourceSlot I = grabUrnInkSlot I := by
  simp [grabUrnInkSourceSlot, grabUrnInkSlot, grabUrnSourceBase_eq I hsz196]

theorem grabUrnArtSourceSlot_eq (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    grabUrnArtSourceSlot I = grabUrnArtSlot I := by
  simp [grabUrnArtSourceSlot, grabUrnArtSlot, grabUrnSourceBase_eq I hsz196]

theorem grabIlkSourceBase_eq (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    grabIlkSourceBase I = grabIlkBase I := by
  unfold grabIlkSourceBase grabIlkBase ilksBase grabIKey mapSlot solcMappingSlot
  rw [grabIKeyWord_eq I (by omega)]

theorem grabIlkArtSourceSlot_eq (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    grabIlkArtSourceSlot I = grabIlkArtSlot I := by
  simp [grabIlkArtSourceSlot, grabIlkArtSlot, grabIlkSourceBase_eq I hsz196]

theorem grabIlkRateSourceSlot_eq (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    grabIlkRateSourceSlot I = grabIlkRateSlot I := by
  simp [grabIlkRateSourceSlot, grabIlkRateSlot, grabIlkSourceBase_eq I hsz196]

theorem grabGemSourceBase_eq (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    grabGemSourceBase I = grabGemBase I := by
  unfold grabGemSourceBase grabGemBase gemIlkSlot grabIKey mapSlot solcMappingSlot
  rw [grabIKeyWord_eq I (by omega)]

theorem grabGemSourceSlot_eq (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    grabGemSourceSlot I = grabGemVSlot I := by
  unfold grabGemSourceSlot grabGemVSlot gemSlot grabVKey grabVMaskedWord mapSlot solcMappingSlot
  rw [show gemIlkSlot (grabIKey I) = grabGemBase I from grabGemSourceBase_eq I hsz196,
    keyValueToWord_address_ofNat_mask]

theorem grabSinSourceSlot_eq (I : ExecutionEnv) :
    grabSinSourceSlot I = grabSinSlot I := by
  unfold grabSinSourceSlot grabSinSlot sinSlot grabWKey grabWMaskedWord mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem grabSourceLoad_urnInk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (grabUrnInkSourceSlot I) =
      vatSlotWord (grabUrnInkSlot I) σ I := by
  simp [initState, Solm.EVM.storageLoad, vatSlotWord, solcSlotWord,
    State.lookupAccount, Account.lookupStorage, grabUrnInkSourceSlot_eq I hsz196]

theorem grabSourceLoad_urnArt {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (grabUrnArtSourceSlot I) =
      vatSlotWord (grabUrnArtSlot I) σ I := by
  simp [initState, Solm.EVM.storageLoad, vatSlotWord, solcSlotWord,
    State.lookupAccount, Account.lookupStorage, grabUrnArtSourceSlot_eq I hsz196]

theorem grabSourceLoad_ilkArt {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (grabIlkArtSourceSlot I) =
      vatSlotWord (grabIlkArtSlot I) σ I := by
  simp [initState, Solm.EVM.storageLoad, vatSlotWord, solcSlotWord,
    State.lookupAccount, Account.lookupStorage, grabIlkArtSourceSlot_eq I hsz196]

theorem grabSourceLoad_ilkRate {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (grabIlkRateSourceSlot I) =
      vatSlotWord (grabIlkRateSlot I) σ I := by
  simp [initState, Solm.EVM.storageLoad, vatSlotWord, solcSlotWord,
    State.lookupAccount, Account.lookupStorage, grabIlkRateSourceSlot_eq I hsz196]

theorem grabSourceLoad_gem {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (grabGemSourceSlot I) =
      vatSlotWord (grabGemVSlot I) σ I := by
  simp [initState, Solm.EVM.storageLoad, vatSlotWord, solcSlotWord,
    State.lookupAccount, Account.lookupStorage, grabGemSourceSlot_eq I hsz196]

theorem grabSourceLoad_sin {cA gh bl σ σ₀ A I} {g : UInt256} :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (grabSinSourceSlot I) =
      vatSlotWord (grabSinSlot I) σ I := by
  simp [initState, Solm.EVM.storageLoad, vatSlotWord, solcSlotWord,
    State.lookupAccount, Account.lookupStorage, grabSinSourceSlot_eq I]

theorem grabSourceLoad_vice {cA gh bl σ σ₀ A I} {g : UInt256} :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        grabViceSourceSlot =
      vatSlotWord ⟨8⟩ σ I := by
  simp [initState, Solm.EVM.storageLoad, vatSlotWord, solcSlotWord,
    State.lookupAccount, Account.lookupStorage, grabViceSourceSlot]

theorem grabSourceLoad_urnArt_staged {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) :
    let evm1 := grabSourceEvm1 cA gh bl σ σ₀ A I g (grabUrnInkNew σ I)
    Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner (grabUrnArtSourceSlot I) =
      solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I) := by
  intro evm1
  simp [evm1, grabSourceEvm1, grabSourceEvm0, initState, storageStore_accountMap,
    storageStore_executionEnv, Solm.EVM.storageLoad, solcSlotWord, grabAfterUrnInk,
    State.lookupAccount, Account.lookupStorage, grabUrnInkSourceSlot_eq I hsz196,
    grabUrnArtSourceSlot_eq I hsz196]

theorem grabSourceLoad_ilkArt_staged {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) :
    let evm2 := grabSourceEvm2 cA gh bl σ σ₀ A I g
      (grabUrnInkNew σ I) (grabUrnArtNew σ I)
    Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner (grabIlkArtSourceSlot I) =
      solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I) := by
  intro evm2
  simp [evm2, grabSourceEvm2, grabSourceEvm1, grabSourceEvm0, initState,
    storageStore_accountMap, storageStore_executionEnv, Solm.EVM.storageLoad,
    solcSlotWord, grabAfterUrnArt, grabAfterUrnInk, State.lookupAccount,
    Account.lookupStorage, grabUrnInkSourceSlot_eq I hsz196,
    grabUrnArtSourceSlot_eq I hsz196, grabIlkArtSourceSlot_eq I hsz196]

theorem grabSourceLoad_ilkRate_staged {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) :
    let evm3 := grabSourceEvm3 cA gh bl σ σ₀ A I g
      (grabUrnInkNew σ I) (grabUrnArtNew σ I) (grabIlkArtNew σ I)
    Solm.EVM.storageLoad evm3 evm3.executionEnv.codeOwner (grabIlkRateSourceSlot I) =
      solcSlotWord (grabAfterIlkArt σ I) I (grabIlkRateSlot I) := by
  intro evm3
  simp [evm3, grabSourceEvm3, grabSourceEvm2, grabSourceEvm1, grabSourceEvm0, initState,
    storageStore_accountMap, storageStore_executionEnv, Solm.EVM.storageLoad,
    solcSlotWord, grabAfterIlkArt, grabAfterUrnArt, grabAfterUrnInk,
    State.lookupAccount, Account.lookupStorage, grabUrnInkSourceSlot_eq I hsz196,
    grabUrnArtSourceSlot_eq I hsz196, grabIlkArtSourceSlot_eq I hsz196,
    grabIlkRateSourceSlot_eq I hsz196]

theorem grabSourceLoad_gem_staged {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) :
    let evm3 := grabSourceEvm3 cA gh bl σ σ₀ A I g
      (grabUrnInkNew σ I) (grabUrnArtNew σ I) (grabIlkArtNew σ I)
    Solm.EVM.storageLoad evm3 evm3.executionEnv.codeOwner (grabGemSourceSlot I) =
      solcSlotWord (grabAfterIlkArt σ I) I (grabGemVSlot I) := by
  intro evm3
  simp [evm3, grabSourceEvm3, grabSourceEvm2, grabSourceEvm1, grabSourceEvm0, initState,
    storageStore_accountMap, storageStore_executionEnv, Solm.EVM.storageLoad,
    solcSlotWord, grabAfterIlkArt, grabAfterUrnArt, grabAfterUrnInk,
    State.lookupAccount, Account.lookupStorage, grabUrnInkSourceSlot_eq I hsz196,
    grabUrnArtSourceSlot_eq I hsz196, grabIlkArtSourceSlot_eq I hsz196,
    grabGemSourceSlot_eq I hsz196]

theorem grabSourceLoad_sin_staged {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) :
    let evm4 := grabSourceEvm4 cA gh bl σ σ₀ A I g
      (grabUrnInkNew σ I) (grabUrnArtNew σ I) (grabIlkArtNew σ I)
      (grabGemNew σ I)
    Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner (grabSinSourceSlot I) =
      solcSlotWord (grabAfterGem σ I) I (grabSinSlot I) := by
  intro evm4
  simp [evm4, grabSourceEvm4, grabSourceEvm3, grabSourceEvm2, grabSourceEvm1,
    grabSourceEvm0, initState, storageStore_accountMap, storageStore_executionEnv,
    Solm.EVM.storageLoad, solcSlotWord, grabAfterGem, grabAfterIlkArt,
    grabAfterUrnArt, grabAfterUrnInk, State.lookupAccount, Account.lookupStorage,
    grabUrnInkSourceSlot_eq I hsz196, grabUrnArtSourceSlot_eq I hsz196,
    grabIlkArtSourceSlot_eq I hsz196, grabGemSourceSlot_eq I hsz196,
    grabSinSourceSlot_eq I]

theorem grabSourceLoad_vice_staged {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) :
    let evm5 := grabSourceEvm5 cA gh bl σ σ₀ A I g
      (grabUrnInkNew σ I) (grabUrnArtNew σ I) (grabIlkArtNew σ I)
      (grabGemNew σ I) (grabSinNew σ I)
    Solm.EVM.storageLoad evm5 evm5.executionEnv.codeOwner grabViceSourceSlot =
      solcSlotWord (grabAfterSin σ I) I ⟨8⟩ := by
  intro evm5
  simp [evm5, grabSourceEvm5, grabSourceEvm4, grabSourceEvm3, grabSourceEvm2,
    grabSourceEvm1, grabSourceEvm0, initState, storageStore_accountMap,
    storageStore_executionEnv, Solm.EVM.storageLoad, solcSlotWord, grabAfterSin,
    grabAfterGem, grabAfterIlkArt, grabAfterUrnArt, grabAfterUrnInk,
    State.lookupAccount, Account.lookupStorage, grabUrnInkSourceSlot_eq I hsz196,
    grabUrnArtSourceSlot_eq I hsz196, grabIlkArtSourceSlot_eq I hsz196,
    grabGemSourceSlot_eq I hsz196, grabSinSourceSlot_eq I, grabViceSourceSlot]

theorem accountMapEquiv_grabSourceFinal
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hsz196 : 196 ≤ I.calldata.size)
    (urnInkNew urnArtNew ilkArtNew gemNew sinNew viceNew : UInt256)
    (hInk : urnInkNew = grabUrnInkNew σ I)
    (hArt : urnArtNew = grabUrnArtNew σ I)
    (hIlk : ilkArtNew = grabIlkArtNew σ I)
    (hGem : gemNew = grabGemNew σ I)
    (hSin : sinNew = grabSinNew σ I)
    (hVice : viceNew = grabViceNew σ I) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
      (grabUrnInkSourceSlot I) urnInkNew
    let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
      (grabUrnArtSourceSlot I) urnArtNew
    let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
      (grabIlkArtSourceSlot I) ilkArtNew
    let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
      (grabGemSourceSlot I) gemNew
    let evm5 := Solm.EVM.storageStore evm4 evm4.executionEnv.codeOwner
      (grabSinSourceSlot I) sinNew
    let evm6 := Solm.EVM.storageStore evm5 evm5.executionEnv.codeOwner
      grabViceSourceSlot viceNew
    accountMapEquiv (grabAfterVice σ I) evm6.accountMap := by
  intro evm0 evm1 evm2 evm3 evm4 evm5 evm6
  have h0 : accountMapEquiv σ σ := accountMapEquiv_refl σ
  have h1 : accountMapEquiv (grabAfterUrnInk σ I) evm1.accountMap := by
    simpa [evm1, evm0, initState, storageStore_accountMap, grabAfterUrnInk,
      grabUrnInkSourceSlot_eq I hsz196, hInk] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (grabUrnInkSlot I)
        (grabUrnInkNew σ I) h0
  have h2 : accountMapEquiv (grabAfterUrnArt σ I) evm2.accountMap := by
    simpa [evm2, evm1, evm0, initState, storageStore_accountMap,
      storageStore_executionEnv, grabAfterUrnArt, grabUrnArtSourceSlot_eq I hsz196,
      hArt] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (grabUrnArtSlot I)
        (grabUrnArtNew σ I) h1
  have h3 : accountMapEquiv (grabAfterIlkArt σ I) evm3.accountMap := by
    simpa [evm3, evm2, evm1, evm0, initState, storageStore_accountMap,
      storageStore_executionEnv, grabAfterIlkArt, grabIlkArtSourceSlot_eq I hsz196,
      hIlk] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (grabIlkArtSlot I)
        (grabIlkArtNew σ I) h2
  have h4 : accountMapEquiv (grabAfterGem σ I) evm4.accountMap := by
    simpa [evm4, evm3, evm2, evm1, evm0, initState, storageStore_accountMap,
      storageStore_executionEnv, grabAfterGem, grabGemSourceSlot_eq I hsz196, hGem]
      using
      accountMapEquiv_sstoreAccountMap I.codeOwner (grabGemVSlot I)
        (grabGemNew σ I) h3
  have h5 : accountMapEquiv (grabAfterSin σ I) evm5.accountMap := by
    simpa [evm5, evm4, evm3, evm2, evm1, evm0, initState, storageStore_accountMap,
      storageStore_executionEnv, grabAfterSin, grabSinSourceSlot_eq I, hSin] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (grabSinSlot I)
        (grabSinNew σ I) h4
  simpa [evm6, evm5, evm4, evm3, evm2, evm1, evm0, initState,
    storageStore_accountMap, storageStore_executionEnv, grabAfterVice, grabViceSourceSlot,
    hVice] using
    accountMapEquiv_sstoreAccountMap I.codeOwner (⟨8⟩ : UInt256)
      (grabViceNew σ I) h5

theorem grabSourceFinal_createdAccounts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (urnInkNew urnArtNew ilkArtNew gemNew sinNew viceNew : UInt256) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
      (grabUrnInkSourceSlot I) urnInkNew
    let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
      (grabUrnArtSourceSlot I) urnArtNew
    let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
      (grabIlkArtSourceSlot I) ilkArtNew
    let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
      (grabGemSourceSlot I) gemNew
    let evm5 := Solm.EVM.storageStore evm4 evm4.executionEnv.codeOwner
      (grabSinSourceSlot I) sinNew
    let evm6 := Solm.EVM.storageStore evm5 evm5.executionEnv.codeOwner
      grabViceSourceSlot viceNew
    (cA, grabAfterVice σ I).1 = evm6.createdAccounts := by
  intro evm0 evm1 evm2 evm3 evm4 evm5 evm6
  simp [evm6, evm5, evm4, evm3, evm2, evm1, evm0, initState,
    storageStore_createdAccounts]

theorem grabStorageType_urn_ink (I : ExecutionEnv) :
    storageTypeAt? contract.storage (grabUrnInkEvaledRef I) =
      some (.elem (.int uint256Int)) := by
  simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, UrnStructTy, uint256St]

theorem grabStorageType_urn_art (I : ExecutionEnv) :
    storageTypeAt? contract.storage (grabUrnArtEvaledRef I) =
      some (.elem (.int uint256Int)) := by
  simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, UrnStructTy, uint256St]

theorem grabStorageType_ilk_art (I : ExecutionEnv) :
    storageTypeAt? contract.storage (grabIlkArtEvaledRef I) =
      some (.elem (.int uint256Int)) := by
  simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, IlkStructTy, uint256St]

theorem grabStorageType_ilk_rate (I : ExecutionEnv) :
    storageTypeAt? contract.storage (grabIlkRateEvaledRef I) =
      some (.elem (.int uint256Int)) := by
  simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, IlkStructTy, uint256St]

theorem grabStorageType_gem (I : ExecutionEnv) :
    storageTypeAt? contract.storage (grabGemEvaledRef I) =
      some (.elem (.int uint256Int)) := by
  simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]

theorem grabStorageType_sin (I : ExecutionEnv) :
    storageTypeAt? contract.storage (grabSinEvaledRef I) =
      some (.elem (.int uint256Int)) := by
  simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]

theorem grabStorageType_vice :
    storageTypeAt? contract.storage grabViceEvaledRef =
      some (.elem (.int uint256Int)) := by
  simp [storageTypeAt?, contract, storageDecls, uint256St]

theorem grabStorageLayout_urn_ink_source (I : ExecutionEnv) :
    config.storage.layout (grabUrnInkEvaledRef I) =
      fun _ => some (wordLoc (grabUrnInkSourceSlot I)) := by
  funext evm
  change storageLayoutRaw (grabUrnInkEvaledRef I) evm =
    some (wordLoc (grabUrnInkSourceSlot I))
  simp [storageLayoutRaw, grabUrnInkEvaledRef, grabUrnInkSourceSlot, grabUrnSourceBase]

theorem grabStorageLayout_urn_art_source (I : ExecutionEnv) :
    config.storage.layout (grabUrnArtEvaledRef I) =
      fun _ => some (wordLoc (grabUrnArtSourceSlot I)) := by
  funext evm
  change storageLayoutRaw (grabUrnArtEvaledRef I) evm =
    some (wordLoc (grabUrnArtSourceSlot I))
  simp [storageLayoutRaw, grabUrnArtEvaledRef, grabUrnArtSourceSlot, grabUrnSourceBase]

theorem grabStorageLayout_ilk_art_source (I : ExecutionEnv) :
    config.storage.layout (grabIlkArtEvaledRef I) =
      fun _ => some (wordLoc (grabIlkArtSourceSlot I)) := by
  funext evm
  change storageLayoutRaw (grabIlkArtEvaledRef I) evm =
    some (wordLoc (grabIlkArtSourceSlot I))
  simp [storageLayoutRaw, grabIlkArtEvaledRef, grabIlkArtSourceSlot, grabIlkSourceBase]

theorem grabStorageLayout_ilk_rate_source (I : ExecutionEnv) :
    config.storage.layout (grabIlkRateEvaledRef I) =
      fun _ => some (wordLoc (grabIlkRateSourceSlot I)) := by
  funext evm
  change storageLayoutRaw (grabIlkRateEvaledRef I) evm =
    some (wordLoc (grabIlkRateSourceSlot I))
  simp [storageLayoutRaw, grabIlkRateEvaledRef, grabIlkRateSourceSlot, grabIlkSourceBase]

theorem grabStorageLayout_gem_source (I : ExecutionEnv) :
    config.storage.layout (grabGemEvaledRef I) =
      fun _ => some (wordLoc (grabGemSourceSlot I)) := by
  funext evm
  change storageLayoutRaw (grabGemEvaledRef I) evm = some (wordLoc (grabGemSourceSlot I))
  simp [storageLayoutRaw, grabGemEvaledRef, grabGemSourceSlot]

theorem grabStorageLayout_sin_source (I : ExecutionEnv) :
    config.storage.layout (grabSinEvaledRef I) =
      fun _ => some (wordLoc (grabSinSourceSlot I)) := by
  funext evm
  change storageLayoutRaw (grabSinEvaledRef I) evm = some (wordLoc (grabSinSourceSlot I))
  simp [storageLayoutRaw, grabSinEvaledRef, grabSinSourceSlot]

theorem grabStorageLayout_vice_source :
    config.storage.layout grabViceEvaledRef =
      fun _ => some (wordLoc grabViceSourceSlot) := by
  funext evm
  change storageLayoutRaw grabViceEvaledRef evm = some (wordLoc grabViceSourceSlot)
  simp [storageLayoutRaw, grabViceEvaledRef, grabViceSourceSlot]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_grab_urn_ink_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hu : locals.get? "u" = some (grabUValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (urnsF (.var "i") (.var "u") "ink") = .ok (grabUrnInkEvaledRef I) := by
  simp [grabUrnInkEvaledRef, grabIValue, grabUValue, grabIKey, grabUKey,
    urnsF, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
    valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    ← Std.HashMap.get?_eq_getElem?, hi, hu, grabIBytes_len I hsz196]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_grab_urn_art_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hu : locals.get? "u" = some (grabUValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (urnsF (.var "i") (.var "u") "art") = .ok (grabUrnArtEvaledRef I) := by
  simp [grabUrnArtEvaledRef, grabIValue, grabUValue, grabIKey, grabUKey,
    urnsF, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
    valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    ← Std.HashMap.get?_eq_getElem?, hi, hu, grabIBytes_len I hsz196]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_grab_ilk_art_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (ilksF (.var "i") "Art") = .ok (grabIlkArtEvaledRef I) := by
  simp [grabIlkArtEvaledRef, grabIValue, grabIKey, ilksF, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?, hi,
    grabIBytes_len I hsz196]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_grab_ilk_rate_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (ilksF (.var "i") "rate") = .ok (grabIlkRateEvaledRef I) := by
  simp [grabIlkRateEvaledRef, grabIValue, grabIKey, ilksF, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?, hi,
    grabIBytes_len I hsz196]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_grab_gem_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hv : locals.get? "v" = some (grabVValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (gemRef (.var "i") (.var "v")) = .ok (grabGemEvaledRef I) := by
  simp [grabGemEvaledRef, grabIValue, grabVValue, grabIKey, grabVKey,
    gemRef, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
    valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    ← Std.HashMap.get?_eq_getElem?, hi, hv, grabIBytes_len I hsz196]

set_option linter.unusedSimpArgs false in
theorem evalStorageRef_grab_sin_locals (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store)
    (hw : locals.get? "w" = some (grabWValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (sinRef (.var "w")) = .ok (grabSinEvaledRef I) := by
  simp [grabSinEvaledRef, grabWValue, grabWKey, sinRef, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?, hw]

theorem evalStorageRef_grab_vice_locals (evm : EVM.State) (locals : Store) :
    evalStorageRef config { contract := contract, locals := locals } evm viceRef =
      .ok grabViceEvaledRef := by
  simp [grabViceEvaledRef, viceRef, evalStorageRef, evalStorageRefSteps,
    EvalResult.bind, bind, pure]

theorem evalExpr_grab_urn_ink_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hu : locals.get? "u" = some (grabUValue I))
    (hbase : locals.get? "urns" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (urnsF (.var "i") (.var "u") "ink")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grabUrnInkSourceSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_grab_urn_ink_locals evm I locals hsz196 hi hu)
    (hty := grabStorageType_urn_ink I)
    (hloc := grabStorageLayout_urn_ink_source I)
    (hload := vatStorageLocLoad_uint256 evm (grabUrnInkSourceSlot I))

theorem evalExpr_grab_urn_art_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hu : locals.get? "u" = some (grabUValue I))
    (hbase : locals.get? "urns" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (urnsF (.var "i") (.var "u") "art")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grabUrnArtSourceSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_grab_urn_art_locals evm I locals hsz196 hi hu)
    (hty := grabStorageType_urn_art I)
    (hloc := grabStorageLayout_urn_art_source I)
    (hload := vatStorageLocLoad_uint256 evm (grabUrnArtSourceSlot I))

theorem evalExpr_grab_ilk_art_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hbase : locals.get? "ilks" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (ilksF (.var "i") "Art")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grabIlkArtSourceSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_grab_ilk_art_locals evm I locals hsz196 hi)
    (hty := grabStorageType_ilk_art I)
    (hloc := grabStorageLayout_ilk_art_source I)
    (hload := vatStorageLocLoad_uint256 evm (grabIlkArtSourceSlot I))

theorem evalExpr_grab_ilk_rate_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hbase : locals.get? "ilks" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (ilksF (.var "i") "rate")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grabIlkRateSourceSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_grab_ilk_rate_locals evm I locals hsz196 hi)
    (hty := grabStorageType_ilk_rate I)
    (hloc := grabStorageLayout_ilk_rate_source I)
    (hload := vatStorageLocLoad_uint256 evm (grabIlkRateSourceSlot I))

theorem evalExpr_grab_gem_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hv : locals.get? "v" = some (grabVValue I))
    (hbase : locals.get? "gem" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (gemRef (.var "i") (.var "v"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grabGemSourceSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_grab_gem_locals evm I locals hsz196 hi hv)
    (hty := grabStorageType_gem I)
    (hloc := grabStorageLayout_gem_source I)
    (hload := vatStorageLocLoad_uint256 evm (grabGemSourceSlot I))

theorem evalExpr_grab_sin_locals {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (hw : locals.get? "w" = some (grabWValue I))
    (hbase : locals.get? "sin" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (sinRef (.var "w"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (grabSinSourceSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_grab_sin_locals evm I locals hw)
    (hty := grabStorageType_sin I)
    (hloc := grabStorageLayout_sin_source I)
    (hload := vatStorageLocLoad_uint256 evm (grabSinSourceSlot I))

theorem evalExpr_grab_vice_locals {evm : EVM.State} (locals : Store)
    (hbase : locals.get? "vice" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage viceRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner grabViceSourceSlot).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := hbase)
    (her := evalStorageRef_grab_vice_locals evm locals)
    (hty := grabStorageType_vice)
    (hloc := grabStorageLayout_vice_source)
    (hload := vatStorageLocLoad_uint256 evm grabViceSourceSlot)

theorem assignStorageRef_grab_urn_ink (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (urnInkNew : UInt256) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hu : locals.get? "u" = some (grabUValue I))
    (hbase : locals.get? "urns" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (grabUrnInkSourceSlot I) urnInkNew
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (urnsF (.var "i") (.var "u") "ink") (.int (Int.ofNat urnInkNew.toNat)) =
      .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (hbase := hbase)
    (her := evalStorageRef_grab_urn_ink_locals evm I locals hsz196 hi hu)
    (hty := grabStorageType_urn_ink I)
    (hloc := grabStorageLayout_urn_ink_source I)
    (hstore := by simpa [evm'] using
      vatStorageLocStore_uint256 evm (grabUrnInkSourceSlot I) urnInkNew)

theorem assignStorageRef_grab_urn_art (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (urnArtNew : UInt256) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hu : locals.get? "u" = some (grabUValue I))
    (hbase : locals.get? "urns" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (grabUrnArtSourceSlot I) urnArtNew
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (urnsF (.var "i") (.var "u") "art") (.int (Int.ofNat urnArtNew.toNat)) =
      .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (hbase := hbase)
    (her := evalStorageRef_grab_urn_art_locals evm I locals hsz196 hi hu)
    (hty := grabStorageType_urn_art I)
    (hloc := grabStorageLayout_urn_art_source I)
    (hstore := by simpa [evm'] using
      vatStorageLocStore_uint256 evm (grabUrnArtSourceSlot I) urnArtNew)

theorem assignStorageRef_grab_ilk_art (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (ilkArtNew : UInt256) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hbase : locals.get? "ilks" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (grabIlkArtSourceSlot I) ilkArtNew
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (ilksF (.var "i") "Art") (.int (Int.ofNat ilkArtNew.toNat)) =
      .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (hbase := hbase)
    (her := evalStorageRef_grab_ilk_art_locals evm I locals hsz196 hi)
    (hty := grabStorageType_ilk_art I)
    (hloc := grabStorageLayout_ilk_art_source I)
    (hstore := by simpa [evm'] using
      vatStorageLocStore_uint256 evm (grabIlkArtSourceSlot I) ilkArtNew)

theorem assignStorageRef_grab_gem (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (gemNew : UInt256) (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hv : locals.get? "v" = some (grabVValue I))
    (hbase : locals.get? "gem" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (grabGemSourceSlot I) gemNew
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (gemRef (.var "i") (.var "v")) (.int (Int.ofNat gemNew.toNat)) =
      .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (hbase := hbase)
    (her := evalStorageRef_grab_gem_locals evm I locals hsz196 hi hv)
    (hty := grabStorageType_gem I)
    (hloc := grabStorageLayout_gem_source I)
    (hstore := by simpa [evm'] using
      vatStorageLocStore_uint256 evm (grabGemSourceSlot I) gemNew)

theorem assignStorageRef_grab_sin (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store) (sinNew : UInt256)
    (hw : locals.get? "w" = some (grabWValue I))
    (hbase : locals.get? "sin" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (grabSinSourceSlot I) sinNew
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (sinRef (.var "w")) (.int (Int.ofNat sinNew.toNat)) =
      .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (hbase := hbase)
    (her := evalStorageRef_grab_sin_locals evm I locals hw)
    (hty := grabStorageType_sin I)
    (hloc := grabStorageLayout_sin_source I)
    (hstore := by simpa [evm'] using
      vatStorageLocStore_uint256 evm (grabSinSourceSlot I) sinNew)

theorem assignStorageRef_grab_vice (evm : EVM.State)
    (locals : Store) (viceNew : UInt256)
    (hbase : locals.get? "vice" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      grabViceSourceSlot viceNew
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      viceRef (.int (Int.ofNat viceNew.toNat)) =
      .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (hbase := hbase)
    (her := evalStorageRef_grab_vice_locals evm locals)
    (hty := grabStorageType_vice)
    (hloc := grabStorageLayout_vice_source)
    (hstore := by simpa [evm'] using
      vatStorageLocStore_uint256 evm grabViceSourceSlot viceNew)

theorem execGrabUrnInkUpdateOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (urnInkOld urnInkNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hu : locals.get? "u" = some (grabUValue I))
    (hdink : locals.get? "dink" = some (grabDinkValue I))
    (hbase : locals.get? "urns" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabUrnInkSourceSlot I) = urnInkOld)
    (hnew : urnInkNew = grabDinkWord I + urnInkOld)
    (hguardNeg : 0 ≤ grabDinkInt I ∨ urnInkNew.toNat ≤ urnInkOld.toNat)
    (hguardPos : grabDinkInt I ≤ 0 ∨ urnInkOld.toNat ≤ urnInkNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "urnInkNew" (.storage (urnsF (.var "i") (.var "u") "ink"))
        (.var "dink") ++
        [ .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew") ])
      (.ok
        { contract := contract,
          locals := locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat)) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (grabUrnInkSourceSlot I) urnInkNew)) := by
  let locals' := locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (grabUrnInkSourceSlot I) urnInkNew
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "i") (.var "u") "ink")) =
        .ok (.int (Int.ofNat urnInkOld.toNat)) := by
    rw [evalExpr_grab_urn_ink_locals locals hsz196 hi hu hbase, hload]
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (grabDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [grabDinkValue] using hdink)
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256
          (.binary .add (.storage (urnsF (.var "i") (.var "u") "ink")) (.var "dink"))) =
        .ok (.int (Int.ofNat urnInkNew.toNat)) := by
    exact evalExpr_fold_wordWrapAdd_ok hstorage hdinkEval (grabDinkInt_mod_word I) hnew
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "urnInkNew") =
        .ok (.int (Int.ofNat urnInkNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdinkAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dink") =
        .ok (.int (grabDinkInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "dink" =
        some (.int (grabDinkInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [grabDinkValue] using hdink)
  have hiAfter : locals'.get? "i" = some (grabIValue I) := by
    change (locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "i" =
      some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hi
  have huAfter : locals'.get? "u" = some (grabUValue I) := by
    change (locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "u" =
      some (grabUValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hu
  have hbaseAfter : locals'.get? "urns" = none := by
    change (locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "urns" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (urnsF (.var "i") (.var "u") "ink")) =
        .ok (.int (Int.ofNat urnInkOld.toNat)) := by
    rw [evalExpr_grab_urn_ink_locals locals' hsz196 hiAfter huAfter hbaseAfter, hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dink") (.intLit 0))
          (.binary .le (.var "urnInkNew")
            (.storage (urnsF (.var "i") (.var "u") "ink")))) =
        .ok (.bool true) :=
    evalSignedAddGuardNeg_true hdinkAfter hnewEval hstorageAfter hguardNeg
  have hguardPosEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dink") (.intLit 0))
          (.binary .ge (.var "urnInkNew")
            (.storage (urnsF (.var "i") (.var "u") "ink")))) =
        .ok (.bool true) :=
    evalSignedAddGuardPos_true hdinkAfter hnewEval hstorageAfter hguardPos
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals' } evm .storage
        (urnsF (.var "i") (.var "u") "ink") (.int (Int.ofNat urnInkNew.toNat)) =
        .ok ({ contract := contract, locals := locals' }, evm') :=
    assignStorageRef_grab_urn_ink evm I locals' urnInkNew hsz196 hiAfter huAfter hbaseAfter
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "urnInkNew" (some uint256)
        (wordWrap256
          (.binary .add (.storage (urnsF (.var "i") (.var "u") "ink")) (.var "dink"))),
      .require
        (eitherExpr (.binary .ge (.var "dink") (.intLit 0))
          (.binary .le (.var "urnInkNew")
            (.storage (urnsF (.var "i") (.var "u") "ink")))),
      .require
        (eitherExpr (.binary .le (.var "dink") (.intLit 0))
          (.binary .ge (.var "urnInkNew")
            (.storage (urnsF (.var "i") (.var "u") "ink")))),
      .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew") ]
    (.ok { contract := contract, locals := locals' } evm')
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNegEval) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardPosEval) ?_
  exact ExecBlock.consNormal (ExecStmt.assign hnewEval hassign) ExecBlock.nil

theorem execGrabUrnInkCheckedOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (urnInkOld urnInkNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hu : locals.get? "u" = some (grabUValue I))
    (hdink : locals.get? "dink" = some (grabDinkValue I))
    (hbase : locals.get? "urns" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabUrnInkSourceSlot I) = urnInkOld)
    (hnew : urnInkNew = grabDinkWord I + urnInkOld)
    (hguardNeg : 0 ≤ grabDinkInt I ∨ urnInkNew.toNat ≤ urnInkOld.toNat)
    (hguardPos : grabDinkInt I ≤ 0 ∨ urnInkOld.toNat ≤ urnInkNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "urnInkNew" (.storage (urnsF (.var "i") (.var "u") "ink"))
        (.var "dink"))
      (.ok
        { contract := contract,
          locals := locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat)) }
        evm) := by
  let locals' := locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "i") (.var "u") "ink")) =
        .ok (.int (Int.ofNat urnInkOld.toNat)) := by
    rw [evalExpr_grab_urn_ink_locals locals hsz196 hi hu hbase, hload]
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (grabDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [grabDinkValue] using hdink)
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256
          (.binary .add (.storage (urnsF (.var "i") (.var "u") "ink")) (.var "dink"))) =
        .ok (.int (Int.ofNat urnInkNew.toNat)) := by
    exact evalExpr_fold_wordWrapAdd_ok hstorage hdinkEval (grabDinkInt_mod_word I) hnew
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "urnInkNew") =
        .ok (.int (Int.ofNat urnInkNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdinkAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dink") =
        .ok (.int (grabDinkInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "dink" =
        some (.int (grabDinkInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [grabDinkValue] using hdink)
  have hiAfter : locals'.get? "i" = some (grabIValue I) := by
    change (locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "i" =
      some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hi
  have huAfter : locals'.get? "u" = some (grabUValue I) := by
    change (locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "u" =
      some (grabUValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hu
  have hbaseAfter : locals'.get? "urns" = none := by
    change (locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "urns" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (urnsF (.var "i") (.var "u") "ink")) =
        .ok (.int (Int.ofNat urnInkOld.toNat)) := by
    rw [evalExpr_grab_urn_ink_locals locals' hsz196 hiAfter huAfter hbaseAfter, hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dink") (.intLit 0))
          (.binary .le (.var "urnInkNew")
            (.storage (urnsF (.var "i") (.var "u") "ink")))) =
        .ok (.bool true) :=
    evalSignedAddGuardNeg_true hdinkAfter hnewEval hstorageAfter hguardNeg
  have hguardPosEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dink") (.intLit 0))
          (.binary .ge (.var "urnInkNew")
            (.storage (urnsF (.var "i") (.var "u") "ink")))) =
        .ok (.bool true) :=
    evalSignedAddGuardPos_true hdinkAfter hnewEval hstorageAfter hguardPos
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "urnInkNew" (some uint256)
        (wordWrap256
          (.binary .add (.storage (urnsF (.var "i") (.var "u") "ink")) (.var "dink"))),
      .require
        (eitherExpr (.binary .ge (.var "dink") (.intLit 0))
          (.binary .le (.var "urnInkNew")
            (.storage (urnsF (.var "i") (.var "u") "ink")))),
      .require
        (eitherExpr (.binary .le (.var "dink") (.intLit 0))
          (.binary .ge (.var "urnInkNew")
            (.storage (urnsF (.var "i") (.var "u") "ink")))) ]
    (.ok { contract := contract, locals := locals' } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNegEval) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguardPosEval) ExecBlock.nil

theorem execGrabUrnInkCheckedRevertGuardNeg {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (urnInkOld urnInkNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hu : locals.get? "u" = some (grabUValue I))
    (hdink : locals.get? "dink" = some (grabDinkValue I))
    (hbase : locals.get? "urns" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabUrnInkSourceSlot I) = urnInkOld)
    (hnew : urnInkNew = grabDinkWord I + urnInkOld)
    (hguardNeg : grabDinkInt I < 0 ∧ urnInkOld.toNat < urnInkNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "urnInkNew" (.storage (urnsF (.var "i") (.var "u") "ink"))
        (.var "dink"))
      .reverted := by
  let locals' := locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "i") (.var "u") "ink")) =
        .ok (.int (Int.ofNat urnInkOld.toNat)) := by
    rw [evalExpr_grab_urn_ink_locals locals hsz196 hi hu hbase, hload]
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (grabDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [grabDinkValue] using hdink)
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256
          (.binary .add (.storage (urnsF (.var "i") (.var "u") "ink")) (.var "dink"))) =
        .ok (.int (Int.ofNat urnInkNew.toNat)) := by
    exact evalExpr_fold_wordWrapAdd_ok hstorage hdinkEval (grabDinkInt_mod_word I) hnew
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "urnInkNew") =
        .ok (.int (Int.ofNat urnInkNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdinkAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dink") =
        .ok (.int (grabDinkInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "dink" =
        some (.int (grabDinkInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [grabDinkValue] using hdink)
  have hiAfter : locals'.get? "i" = some (grabIValue I) := by
    change (locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "i" =
      some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hi
  have huAfter : locals'.get? "u" = some (grabUValue I) := by
    change (locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "u" =
      some (grabUValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hu
  have hbaseAfter : locals'.get? "urns" = none := by
    change (locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "urns" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (urnsF (.var "i") (.var "u") "ink")) =
        .ok (.int (Int.ofNat urnInkOld.toNat)) := by
    rw [evalExpr_grab_urn_ink_locals locals' hsz196 hiAfter huAfter hbaseAfter, hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dink") (.intLit 0))
          (.binary .le (.var "urnInkNew")
            (.storage (urnsF (.var "i") (.var "u") "ink")))) =
        .ok (.bool false) :=
    evalSignedAddGuardNeg_false hdinkAfter hnewEval hstorageAfter hguardNeg
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "urnInkNew" (some uint256)
        (wordWrap256
          (.binary .add (.storage (urnsF (.var "i") (.var "u") "ink")) (.var "dink"))),
      .require
        (eitherExpr (.binary .ge (.var "dink") (.intLit 0))
          (.binary .le (.var "urnInkNew")
            (.storage (urnsF (.var "i") (.var "u") "ink")))),
      .require
        (eitherExpr (.binary .le (.var "dink") (.intLit 0))
          (.binary .ge (.var "urnInkNew")
            (.storage (urnsF (.var "i") (.var "u") "ink")))) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguardNegEval)

theorem execGrabUrnInkCheckedRevertGuardPos {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (urnInkOld urnInkNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hu : locals.get? "u" = some (grabUValue I))
    (hdink : locals.get? "dink" = some (grabDinkValue I))
    (hbase : locals.get? "urns" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabUrnInkSourceSlot I) = urnInkOld)
    (hnew : urnInkNew = grabDinkWord I + urnInkOld)
    (hguardNeg : 0 ≤ grabDinkInt I ∨ urnInkNew.toNat ≤ urnInkOld.toNat)
    (hguardPos : 0 < grabDinkInt I ∧ urnInkNew.toNat < urnInkOld.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "urnInkNew" (.storage (urnsF (.var "i") (.var "u") "ink"))
        (.var "dink"))
      .reverted := by
  let locals' := locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "i") (.var "u") "ink")) =
        .ok (.int (Int.ofNat urnInkOld.toNat)) := by
    rw [evalExpr_grab_urn_ink_locals locals hsz196 hi hu hbase, hload]
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (grabDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [grabDinkValue] using hdink)
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256
          (.binary .add (.storage (urnsF (.var "i") (.var "u") "ink")) (.var "dink"))) =
        .ok (.int (Int.ofNat urnInkNew.toNat)) := by
    exact evalExpr_fold_wordWrapAdd_ok hstorage hdinkEval (grabDinkInt_mod_word I) hnew
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "urnInkNew") =
        .ok (.int (Int.ofNat urnInkNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdinkAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dink") =
        .ok (.int (grabDinkInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "dink" =
        some (.int (grabDinkInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [grabDinkValue] using hdink)
  have hiAfter : locals'.get? "i" = some (grabIValue I) := by
    change (locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "i" =
      some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hi
  have huAfter : locals'.get? "u" = some (grabUValue I) := by
    change (locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "u" =
      some (grabUValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hu
  have hbaseAfter : locals'.get? "urns" = none := by
    change (locals.insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "urns" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (urnsF (.var "i") (.var "u") "ink")) =
        .ok (.int (Int.ofNat urnInkOld.toNat)) := by
    rw [evalExpr_grab_urn_ink_locals locals' hsz196 hiAfter huAfter hbaseAfter, hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dink") (.intLit 0))
          (.binary .le (.var "urnInkNew")
            (.storage (urnsF (.var "i") (.var "u") "ink")))) =
        .ok (.bool true) :=
    evalSignedAddGuardNeg_true hdinkAfter hnewEval hstorageAfter hguardNeg
  have hguardPosEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dink") (.intLit 0))
          (.binary .ge (.var "urnInkNew")
            (.storage (urnsF (.var "i") (.var "u") "ink")))) =
        .ok (.bool false) :=
    evalSignedAddGuardPos_false hdinkAfter hnewEval hstorageAfter hguardPos
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "urnInkNew" (some uint256)
        (wordWrap256
          (.binary .add (.storage (urnsF (.var "i") (.var "u") "ink")) (.var "dink"))),
      .require
        (eitherExpr (.binary .ge (.var "dink") (.intLit 0))
          (.binary .le (.var "urnInkNew")
            (.storage (urnsF (.var "i") (.var "u") "ink")))),
      .require
        (eitherExpr (.binary .le (.var "dink") (.intLit 0))
          (.binary .ge (.var "urnInkNew")
            (.storage (urnsF (.var "i") (.var "u") "ink")))) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNegEval) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguardPosEval)

theorem execGrabUrnArtCheckedOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (urnArtOld urnArtNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hu : locals.get? "u" = some (grabUValue I))
    (hdart : locals.get? "dart" = some (grabDartValue I))
    (hbase : locals.get? "urns" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabUrnArtSourceSlot I) = urnArtOld)
    (hnew : urnArtNew = grabDartWord I + urnArtOld)
    (hguardNeg : 0 ≤ grabDartInt I ∨ urnArtNew.toNat ≤ urnArtOld.toNat)
    (hguardPos : grabDartInt I ≤ 0 ∨ urnArtOld.toNat ≤ urnArtNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "urnArtNew" (.storage (urnsF (.var "i") (.var "u") "art"))
        (.var "dart"))
      (.ok
        { contract := contract,
          locals := locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat)) }
        evm) := by
  let locals' := locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "i") (.var "u") "art")) =
        .ok (.int (Int.ofNat urnArtOld.toNat)) := by
    rw [evalExpr_grab_urn_art_locals locals hsz196 hi hu hbase, hload]
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (grabDartInt I)) :=
    vatEvalExpr_varInt (by simpa [grabDartValue] using hdart)
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256
          (.binary .add (.storage (urnsF (.var "i") (.var "u") "art")) (.var "dart"))) =
        .ok (.int (Int.ofNat urnArtNew.toNat)) := by
    exact evalExpr_fold_wordWrapAdd_ok hstorage hdartEval (grabDartInt_mod_word I) hnew
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "urnArtNew") =
        .ok (.int (Int.ofNat urnArtNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdartAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dart") =
        .ok (.int (grabDartInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "dart" =
        some (.int (grabDartInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [grabDartValue] using hdart)
  have hiAfter : locals'.get? "i" = some (grabIValue I) := by
    change (locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "i" =
      some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hi
  have huAfter : locals'.get? "u" = some (grabUValue I) := by
    change (locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "u" =
      some (grabUValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hu
  have hbaseAfter : locals'.get? "urns" = none := by
    change (locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "urns" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (urnsF (.var "i") (.var "u") "art")) =
        .ok (.int (Int.ofNat urnArtOld.toNat)) := by
    rw [evalExpr_grab_urn_art_locals locals' hsz196 hiAfter huAfter hbaseAfter, hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
          (.binary .le (.var "urnArtNew")
            (.storage (urnsF (.var "i") (.var "u") "art")))) =
        .ok (.bool true) :=
    evalSignedAddGuardNeg_true hdartAfter hnewEval hstorageAfter hguardNeg
  have hguardPosEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dart") (.intLit 0))
          (.binary .ge (.var "urnArtNew")
            (.storage (urnsF (.var "i") (.var "u") "art")))) =
        .ok (.bool true) :=
    evalSignedAddGuardPos_true hdartAfter hnewEval hstorageAfter hguardPos
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "urnArtNew" (some uint256)
        (wordWrap256
          (.binary .add (.storage (urnsF (.var "i") (.var "u") "art")) (.var "dart"))),
      .require
        (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
          (.binary .le (.var "urnArtNew")
            (.storage (urnsF (.var "i") (.var "u") "art")))),
      .require
        (eitherExpr (.binary .le (.var "dart") (.intLit 0))
          (.binary .ge (.var "urnArtNew")
            (.storage (urnsF (.var "i") (.var "u") "art")))) ]
    (.ok { contract := contract, locals := locals' } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNegEval) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguardPosEval) ExecBlock.nil

theorem execGrabUrnArtCheckedRevertGuardNeg {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (urnArtOld urnArtNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hu : locals.get? "u" = some (grabUValue I))
    (hdart : locals.get? "dart" = some (grabDartValue I))
    (hbase : locals.get? "urns" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabUrnArtSourceSlot I) = urnArtOld)
    (hnew : urnArtNew = grabDartWord I + urnArtOld)
    (hguardNeg : grabDartInt I < 0 ∧ urnArtOld.toNat < urnArtNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "urnArtNew" (.storage (urnsF (.var "i") (.var "u") "art"))
        (.var "dart"))
      .reverted := by
  let locals' := locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "i") (.var "u") "art")) =
        .ok (.int (Int.ofNat urnArtOld.toNat)) := by
    rw [evalExpr_grab_urn_art_locals locals hsz196 hi hu hbase, hload]
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (grabDartInt I)) :=
    vatEvalExpr_varInt (by simpa [grabDartValue] using hdart)
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256
          (.binary .add (.storage (urnsF (.var "i") (.var "u") "art")) (.var "dart"))) =
        .ok (.int (Int.ofNat urnArtNew.toNat)) := by
    exact evalExpr_fold_wordWrapAdd_ok hstorage hdartEval (grabDartInt_mod_word I) hnew
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "urnArtNew") =
        .ok (.int (Int.ofNat urnArtNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdartAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dart") =
        .ok (.int (grabDartInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "dart" =
        some (.int (grabDartInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [grabDartValue] using hdart)
  have hiAfter : locals'.get? "i" = some (grabIValue I) := by
    change (locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "i" =
      some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hi
  have huAfter : locals'.get? "u" = some (grabUValue I) := by
    change (locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "u" =
      some (grabUValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hu
  have hbaseAfter : locals'.get? "urns" = none := by
    change (locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "urns" =
      none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (urnsF (.var "i") (.var "u") "art")) =
        .ok (.int (Int.ofNat urnArtOld.toNat)) := by
    rw [evalExpr_grab_urn_art_locals locals' hsz196 hiAfter huAfter hbaseAfter, hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
          (.binary .le (.var "urnArtNew")
            (.storage (urnsF (.var "i") (.var "u") "art")))) =
        .ok (.bool false) :=
    evalSignedAddGuardNeg_false hdartAfter hnewEval hstorageAfter hguardNeg
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "urnArtNew" (some uint256)
        (wordWrap256
          (.binary .add (.storage (urnsF (.var "i") (.var "u") "art")) (.var "dart"))),
      .require
        (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
          (.binary .le (.var "urnArtNew")
            (.storage (urnsF (.var "i") (.var "u") "art")))),
      .require
        (eitherExpr (.binary .le (.var "dart") (.intLit 0))
          (.binary .ge (.var "urnArtNew")
            (.storage (urnsF (.var "i") (.var "u") "art")))) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguardNegEval)

theorem execGrabUrnArtCheckedRevertGuardPos {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (urnArtOld urnArtNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hu : locals.get? "u" = some (grabUValue I))
    (hdart : locals.get? "dart" = some (grabDartValue I))
    (hbase : locals.get? "urns" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabUrnArtSourceSlot I) = urnArtOld)
    (hnew : urnArtNew = grabDartWord I + urnArtOld)
    (hguardNeg : 0 ≤ grabDartInt I ∨ urnArtNew.toNat ≤ urnArtOld.toNat)
    (hguardPos : 0 < grabDartInt I ∧ urnArtNew.toNat < urnArtOld.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "urnArtNew" (.storage (urnsF (.var "i") (.var "u") "art"))
        (.var "dart"))
      .reverted := by
  let locals' := locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (urnsF (.var "i") (.var "u") "art")) =
        .ok (.int (Int.ofNat urnArtOld.toNat)) := by
    rw [evalExpr_grab_urn_art_locals locals hsz196 hi hu hbase, hload]
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (grabDartInt I)) :=
    vatEvalExpr_varInt (by simpa [grabDartValue] using hdart)
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256
          (.binary .add (.storage (urnsF (.var "i") (.var "u") "art")) (.var "dart"))) =
        .ok (.int (Int.ofNat urnArtNew.toNat)) := by
    exact evalExpr_fold_wordWrapAdd_ok hstorage hdartEval (grabDartInt_mod_word I) hnew
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "urnArtNew") =
        .ok (.int (Int.ofNat urnArtNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdartAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dart") =
        .ok (.int (grabDartInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "dart" =
        some (.int (grabDartInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [grabDartValue] using hdart)
  have hiAfter : locals'.get? "i" = some (grabIValue I) := by
    change (locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "i" =
      some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hi
  have huAfter : locals'.get? "u" = some (grabUValue I) := by
    change (locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "u" =
      some (grabUValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hu
  have hbaseAfter : locals'.get? "urns" = none := by
    change (locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "urns" =
      none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (urnsF (.var "i") (.var "u") "art")) =
        .ok (.int (Int.ofNat urnArtOld.toNat)) := by
    rw [evalExpr_grab_urn_art_locals locals' hsz196 hiAfter huAfter hbaseAfter, hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
          (.binary .le (.var "urnArtNew")
            (.storage (urnsF (.var "i") (.var "u") "art")))) =
        .ok (.bool true) :=
    evalSignedAddGuardNeg_true hdartAfter hnewEval hstorageAfter hguardNeg
  have hguardPosEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dart") (.intLit 0))
          (.binary .ge (.var "urnArtNew")
            (.storage (urnsF (.var "i") (.var "u") "art")))) =
        .ok (.bool false) :=
    evalSignedAddGuardPos_false hdartAfter hnewEval hstorageAfter hguardPos
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "urnArtNew" (some uint256)
        (wordWrap256
          (.binary .add (.storage (urnsF (.var "i") (.var "u") "art")) (.var "dart"))),
      .require
        (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
          (.binary .le (.var "urnArtNew")
            (.storage (urnsF (.var "i") (.var "u") "art")))),
      .require
        (eitherExpr (.binary .le (.var "dart") (.intLit 0))
          (.binary .ge (.var "urnArtNew")
            (.storage (urnsF (.var "i") (.var "u") "art")))) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNegEval) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguardPosEval)

theorem execGrabIlkArtCheckedOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (ilkArtOld ilkArtNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hdart : locals.get? "dart" = some (grabDartValue I))
    (hbase : locals.get? "ilks" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabIlkArtSourceSlot I) = ilkArtOld)
    (hnew : ilkArtNew = grabDartWord I + ilkArtOld)
    (hguardNeg : 0 ≤ grabDartInt I ∨ ilkArtNew.toNat ≤ ilkArtOld.toNat)
    (hguardPos : grabDartInt I ≤ 0 ∨ ilkArtOld.toNat ≤ ilkArtNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "ilkArtNew" (.storage (ilksF (.var "i") "Art")) (.var "dart"))
      (.ok
        { contract := contract,
          locals := locals.insert "ilkArtNew" (.int (Int.ofNat ilkArtNew.toNat)) }
        evm) := by
  let locals' := locals.insert "ilkArtNew" (.int (Int.ofNat ilkArtNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "i") "Art")) =
        .ok (.int (Int.ofNat ilkArtOld.toNat)) := by
    rw [evalExpr_grab_ilk_art_locals locals hsz196 hi hbase, hload]
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (grabDartInt I)) :=
    vatEvalExpr_varInt (by simpa [grabDartValue] using hdart)
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256 (.binary .add (.storage (ilksF (.var "i") "Art")) (.var "dart"))) =
        .ok (.int (Int.ofNat ilkArtNew.toNat)) := by
    exact evalExpr_fold_wordWrapAdd_ok hstorage hdartEval (grabDartInt_mod_word I) hnew
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "ilkArtNew") =
        .ok (.int (Int.ofNat ilkArtNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdartAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dart") =
        .ok (.int (grabDartInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "ilkArtNew" (.int (Int.ofNat ilkArtNew.toNat))).get? "dart" =
        some (.int (grabDartInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [grabDartValue] using hdart)
  have hiAfter : locals'.get? "i" = some (grabIValue I) := by
    change (locals.insert "ilkArtNew" (.int (Int.ofNat ilkArtNew.toNat))).get? "i" =
      some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hi
  have hbaseAfter : locals'.get? "ilks" = none := by
    change (locals.insert "ilkArtNew" (.int (Int.ofNat ilkArtNew.toNat))).get? "ilks" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (ilksF (.var "i") "Art")) =
        .ok (.int (Int.ofNat ilkArtOld.toNat)) := by
    rw [evalExpr_grab_ilk_art_locals locals' hsz196 hiAfter hbaseAfter, hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
          (.binary .le (.var "ilkArtNew") (.storage (ilksF (.var "i") "Art")))) =
        .ok (.bool true) :=
    evalSignedAddGuardNeg_true hdartAfter hnewEval hstorageAfter hguardNeg
  have hguardPosEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dart") (.intLit 0))
          (.binary .ge (.var "ilkArtNew") (.storage (ilksF (.var "i") "Art")))) =
        .ok (.bool true) :=
    evalSignedAddGuardPos_true hdartAfter hnewEval hstorageAfter hguardPos
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "ilkArtNew" (some uint256)
        (wordWrap256 (.binary .add (.storage (ilksF (.var "i") "Art")) (.var "dart"))),
      .require
        (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
          (.binary .le (.var "ilkArtNew") (.storage (ilksF (.var "i") "Art")))),
      .require
        (eitherExpr (.binary .le (.var "dart") (.intLit 0))
          (.binary .ge (.var "ilkArtNew") (.storage (ilksF (.var "i") "Art")))) ]
    (.ok { contract := contract, locals := locals' } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNegEval) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguardPosEval) ExecBlock.nil

theorem execGrabDtabMulCheckedOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (rateOld : UInt256) (dtab : Int)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hdart : locals.get? "dart" = some (grabDartValue I))
    (hbase : locals.get? "ilks" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabIlkRateSourceSlot I) = rateOld)
    (hdtab : dtab = Int.ofNat rateOld.toNat * grabDartInt I)
    (hdtabLo : -((2 : Int) ^ 255) ≤ dtab)
    (hdtabHi : dtab < (2 : Int) ^ 255)
    (hguardMax :
      evalExpr? config
        { contract := contract,
          locals := locals.insert "dtab" (.int dtab) } evm
        (.binary .le (.storage (ilksF (.var "i") "rate")) (.intLit maxInt256)) =
        .ok (.bool true))
    (hguardMul :
      evalExpr? config
        { contract := contract,
          locals := locals.insert "dtab" (.int dtab) } evm
        (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
          (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
            (.storage (ilksF (.var "i") "rate")))) =
        .ok (.bool true)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulSignedInto "dtab" (.storage (ilksF (.var "i") "rate")) (.var "dart"))
      (.ok
        { contract := contract, locals := locals.insert "dtab" (.int dtab) }
        evm) := by
  let locals' := locals.insert "dtab" (.int dtab)
  have hrate :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "i") "rate")) =
        .ok (.int (Int.ofNat rateOld.toNat)) := by
    rw [evalExpr_grab_ilk_rate_locals locals hsz196 hi hbase, hload]
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (grabDartInt I)) :=
    vatEvalExpr_varInt (by simpa [grabDartValue] using hdart)
  have hmul :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .mul (.storage (ilksF (.var "i") "rate")) (.var "dart")) =
        .ok (.int dtab) :=
    evalExpr_fold_mul_int_ok hrate hdartEval hdtab
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (s256 (.binary .mul (.storage (ilksF (.var "i") "rate")) (.var "dart"))) =
        .ok (.int dtab) :=
    evalExpr_fold_s256_ok hmul hdtabLo hdtabHi
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "dtab" (some int256)
        (s256 (.binary .mul (.storage (ilksF (.var "i") "rate")) (.var "dart"))),
      .require (.binary .le (.storage (ilksF (.var "i") "rate")) (.intLit maxInt256)),
      .require
        (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
          (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
            (.storage (ilksF (.var "i") "rate")))) ]
    (.ok { contract := contract, locals := locals' } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardMax) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguardMul) ExecBlock.nil

theorem execGrabDtabMulCheckedRevertRange {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (rateOld : UInt256) (dtab : Int)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hdart : locals.get? "dart" = some (grabDartValue I))
    (hbase : locals.get? "ilks" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabIlkRateSourceSlot I) = rateOld)
    (hdtab : dtab = Int.ofNat rateOld.toNat * grabDartInt I)
    (hbad : dtab < -((2 : Int) ^ 255) ∨ dtab ≥ (2 : Int) ^ 255) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulSignedInto "dtab" (.storage (ilksF (.var "i") "rate")) (.var "dart"))
      .reverted := by
  have hrate :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "i") "rate")) =
        .ok (.int (Int.ofNat rateOld.toNat)) := by
    rw [evalExpr_grab_ilk_rate_locals locals hsz196 hi hbase, hload]
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (grabDartInt I)) :=
    vatEvalExpr_varInt (by simpa [grabDartValue] using hdart)
  have hmul :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .mul (.storage (ilksF (.var "i") "rate")) (.var "dart")) =
        .ok (.int dtab) :=
    evalExpr_fold_mul_int_ok hrate hdartEval hdtab
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "dtab" (some int256)
        (s256 (.binary .mul (.storage (ilksF (.var "i") "rate")) (.var "dart"))),
      .require (.binary .le (.storage (ilksF (.var "i") "rate")) (.intLit maxInt256)),
      .require
        (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
          (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
            (.storage (ilksF (.var "i") "rate")))) ]
    .reverted
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert (evalExpr_s256_revert hmul hbad))

theorem execGrabDtabMulCheckedRevertMax {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (rateOld : UInt256) (dtab : Int)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hdart : locals.get? "dart" = some (grabDartValue I))
    (hbase : locals.get? "ilks" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabIlkRateSourceSlot I) = rateOld)
    (hdtab : dtab = Int.ofNat rateOld.toNat * grabDartInt I)
    (hdtabLo : -((2 : Int) ^ 255) ≤ dtab)
    (hdtabHi : dtab < (2 : Int) ^ 255)
    (hguardMax :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) }
        evm (.binary .le (.storage (ilksF (.var "i") "rate")) (.intLit maxInt256)) =
        .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulSignedInto "dtab" (.storage (ilksF (.var "i") "rate")) (.var "dart"))
      .reverted := by
  have hrate :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "i") "rate")) =
        .ok (.int (Int.ofNat rateOld.toNat)) := by
    rw [evalExpr_grab_ilk_rate_locals locals hsz196 hi hbase, hload]
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (grabDartInt I)) :=
    vatEvalExpr_varInt (by simpa [grabDartValue] using hdart)
  have hmul :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .mul (.storage (ilksF (.var "i") "rate")) (.var "dart")) =
        .ok (.int dtab) :=
    evalExpr_fold_mul_int_ok hrate hdartEval hdtab
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (s256 (.binary .mul (.storage (ilksF (.var "i") "rate")) (.var "dart"))) =
        .ok (.int dtab) :=
    evalExpr_fold_s256_ok hmul hdtabLo hdtabHi
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "dtab" (some int256)
        (s256 (.binary .mul (.storage (ilksF (.var "i") "rate")) (.var "dart"))),
      .require (.binary .le (.storage (ilksF (.var "i") "rate")) (.intLit maxInt256)),
      .require
        (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
          (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
            (.storage (ilksF (.var "i") "rate")))) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguardMax)

theorem execGrabDtabMulCheckedRevertMaxSlt {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (rateOld : UInt256) (dtab : Int)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hdart : locals.get? "dart" = some (grabDartValue I))
    (hbase : locals.get? "ilks" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabIlkRateSourceSlot I) = rateOld)
    (hdtab : dtab = Int.ofNat rateOld.toNat * grabDartInt I)
    (hdtabLo : -((2 : Int) ^ 255) ≤ dtab)
    (hdtabHi : dtab < (2 : Int) ^ 255)
    (hmaxFail : UInt256.slt rateOld ⟨0⟩ ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulSignedInto "dtab" (.storage (ilksF (.var "i") "rate")) (.var "dart"))
      .reverted := by
  refine execGrabDtabMulCheckedRevertMax (evm := evm) (I := I) locals rateOld dtab
    hsz196 hi hdart hbase hload hdtab hdtabLo hdtabHi ?_
  let locals' := locals.insert "dtab" (.int dtab)
  have hrate :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (ilksF (.var "i") "rate")) =
        .ok (.int (Int.ofNat rateOld.toNat)) := by
    rw [evalExpr_grab_ilk_rate_locals locals' hsz196]
    · rw [hload]
    · change (locals.insert "dtab" (.int dtab)).get? "i" = some (grabIValue I)
      rw [store_get_ne _ _ (by native_decide)]
      exact hi
    · change (locals.insert "dtab" (.int dtab)).get? "ilks" = none
      rw [store_get_ne _ _ (by native_decide)]
      exact hbase
  exact vatEvalExpr_le_int_false hrate (by simp [evalExpr?, pure])
    (uintWordGtMaxInt256_of_slt_ne_zero hmaxFail)

theorem execGrabDtabMulCheckedRevertMul {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (rateOld : UInt256) (dtab : Int)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hdart : locals.get? "dart" = some (grabDartValue I))
    (hbase : locals.get? "ilks" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabIlkRateSourceSlot I) = rateOld)
    (hdtab : dtab = Int.ofNat rateOld.toNat * grabDartInt I)
    (hdtabLo : -((2 : Int) ^ 255) ≤ dtab)
    (hdtabHi : dtab < (2 : Int) ^ 255)
    (hguardMax :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) }
        evm (.binary .le (.storage (ilksF (.var "i") "rate")) (.intLit maxInt256)) =
        .ok (.bool true))
    (hguardMul :
      evalExpr? config { contract := contract, locals := locals.insert "dtab" (.int dtab) }
        evm
        (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
          (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
            (.storage (ilksF (.var "i") "rate")))) =
        .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedMulSignedInto "dtab" (.storage (ilksF (.var "i") "rate")) (.var "dart"))
      .reverted := by
  have hrate :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "i") "rate")) =
        .ok (.int (Int.ofNat rateOld.toNat)) := by
    rw [evalExpr_grab_ilk_rate_locals locals hsz196 hi hbase, hload]
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (grabDartInt I)) :=
    vatEvalExpr_varInt (by simpa [grabDartValue] using hdart)
  have hmul :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .mul (.storage (ilksF (.var "i") "rate")) (.var "dart")) =
        .ok (.int dtab) :=
    evalExpr_fold_mul_int_ok hrate hdartEval hdtab
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (s256 (.binary .mul (.storage (ilksF (.var "i") "rate")) (.var "dart"))) =
        .ok (.int dtab) :=
    evalExpr_fold_s256_ok hmul hdtabLo hdtabHi
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "dtab" (some int256)
        (s256 (.binary .mul (.storage (ilksF (.var "i") "rate")) (.var "dart"))),
      .require (.binary .le (.storage (ilksF (.var "i") "rate")) (.intLit maxInt256)),
      .require
        (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
          (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
            (.storage (ilksF (.var "i") "rate")))) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardMax) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguardMul)

theorem execGrabIlkArtCheckedRevertGuardNeg {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (ilkArtOld ilkArtNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hdart : locals.get? "dart" = some (grabDartValue I))
    (hbase : locals.get? "ilks" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabIlkArtSourceSlot I) = ilkArtOld)
    (hnew : ilkArtNew = grabDartWord I + ilkArtOld)
    (hguardNeg : grabDartInt I < 0 ∧ ilkArtOld.toNat < ilkArtNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "ilkArtNew" (.storage (ilksF (.var "i") "Art")) (.var "dart"))
      .reverted := by
  let locals' := locals.insert "ilkArtNew" (.int (Int.ofNat ilkArtNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "i") "Art")) =
        .ok (.int (Int.ofNat ilkArtOld.toNat)) := by
    rw [evalExpr_grab_ilk_art_locals locals hsz196 hi hbase, hload]
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (grabDartInt I)) :=
    vatEvalExpr_varInt (by simpa [grabDartValue] using hdart)
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256 (.binary .add (.storage (ilksF (.var "i") "Art")) (.var "dart"))) =
        .ok (.int (Int.ofNat ilkArtNew.toNat)) := by
    exact evalExpr_fold_wordWrapAdd_ok hstorage hdartEval (grabDartInt_mod_word I) hnew
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "ilkArtNew") =
        .ok (.int (Int.ofNat ilkArtNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdartAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dart") =
        .ok (.int (grabDartInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "ilkArtNew" (.int (Int.ofNat ilkArtNew.toNat))).get? "dart" =
        some (.int (grabDartInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [grabDartValue] using hdart)
  have hiAfter : locals'.get? "i" = some (grabIValue I) := by
    change (locals.insert "ilkArtNew" (.int (Int.ofNat ilkArtNew.toNat))).get? "i" =
      some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hi
  have hbaseAfter : locals'.get? "ilks" = none := by
    change (locals.insert "ilkArtNew" (.int (Int.ofNat ilkArtNew.toNat))).get? "ilks" =
      none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (ilksF (.var "i") "Art")) =
        .ok (.int (Int.ofNat ilkArtOld.toNat)) := by
    rw [evalExpr_grab_ilk_art_locals locals' hsz196 hiAfter hbaseAfter, hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
          (.binary .le (.var "ilkArtNew") (.storage (ilksF (.var "i") "Art")))) =
        .ok (.bool false) :=
    evalSignedAddGuardNeg_false hdartAfter hnewEval hstorageAfter hguardNeg
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "ilkArtNew" (some uint256)
        (wordWrap256 (.binary .add (.storage (ilksF (.var "i") "Art")) (.var "dart"))),
      .require
        (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
          (.binary .le (.var "ilkArtNew") (.storage (ilksF (.var "i") "Art")))),
      .require
        (eitherExpr (.binary .le (.var "dart") (.intLit 0))
          (.binary .ge (.var "ilkArtNew") (.storage (ilksF (.var "i") "Art")))) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguardNegEval)

theorem execGrabIlkArtCheckedRevertGuardPos {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (ilkArtOld ilkArtNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hdart : locals.get? "dart" = some (grabDartValue I))
    (hbase : locals.get? "ilks" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabIlkArtSourceSlot I) = ilkArtOld)
    (hnew : ilkArtNew = grabDartWord I + ilkArtOld)
    (hguardNeg : 0 ≤ grabDartInt I ∨ ilkArtNew.toNat ≤ ilkArtOld.toNat)
    (hguardPos : 0 < grabDartInt I ∧ ilkArtNew.toNat < ilkArtOld.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "ilkArtNew" (.storage (ilksF (.var "i") "Art")) (.var "dart"))
      .reverted := by
  let locals' := locals.insert "ilkArtNew" (.int (Int.ofNat ilkArtNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (ilksF (.var "i") "Art")) =
        .ok (.int (Int.ofNat ilkArtOld.toNat)) := by
    rw [evalExpr_grab_ilk_art_locals locals hsz196 hi hbase, hload]
  have hdartEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dart") =
        .ok (.int (grabDartInt I)) :=
    vatEvalExpr_varInt (by simpa [grabDartValue] using hdart)
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256 (.binary .add (.storage (ilksF (.var "i") "Art")) (.var "dart"))) =
        .ok (.int (Int.ofNat ilkArtNew.toNat)) := by
    exact evalExpr_fold_wordWrapAdd_ok hstorage hdartEval (grabDartInt_mod_word I) hnew
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "ilkArtNew") =
        .ok (.int (Int.ofNat ilkArtNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdartAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dart") =
        .ok (.int (grabDartInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "ilkArtNew" (.int (Int.ofNat ilkArtNew.toNat))).get? "dart" =
        some (.int (grabDartInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [grabDartValue] using hdart)
  have hiAfter : locals'.get? "i" = some (grabIValue I) := by
    change (locals.insert "ilkArtNew" (.int (Int.ofNat ilkArtNew.toNat))).get? "i" =
      some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hi
  have hbaseAfter : locals'.get? "ilks" = none := by
    change (locals.insert "ilkArtNew" (.int (Int.ofNat ilkArtNew.toNat))).get? "ilks" =
      none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (ilksF (.var "i") "Art")) =
        .ok (.int (Int.ofNat ilkArtOld.toNat)) := by
    rw [evalExpr_grab_ilk_art_locals locals' hsz196 hiAfter hbaseAfter, hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
          (.binary .le (.var "ilkArtNew") (.storage (ilksF (.var "i") "Art")))) =
        .ok (.bool true) :=
    evalSignedAddGuardNeg_true hdartAfter hnewEval hstorageAfter hguardNeg
  have hguardPosEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dart") (.intLit 0))
          (.binary .ge (.var "ilkArtNew") (.storage (ilksF (.var "i") "Art")))) =
        .ok (.bool false) :=
    evalSignedAddGuardPos_false hdartAfter hnewEval hstorageAfter hguardPos
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "ilkArtNew" (some uint256)
        (wordWrap256 (.binary .add (.storage (ilksF (.var "i") "Art")) (.var "dart"))),
      .require
        (eitherExpr (.binary .ge (.var "dart") (.intLit 0))
          (.binary .le (.var "ilkArtNew") (.storage (ilksF (.var "i") "Art")))),
      .require
        (eitherExpr (.binary .le (.var "dart") (.intLit 0))
          (.binary .ge (.var "ilkArtNew") (.storage (ilksF (.var "i") "Art")))) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNegEval) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguardPosEval)

theorem execGrabGemSubCheckedOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (gemOld gemNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hv : locals.get? "v" = some (grabVValue I))
    (hdink : locals.get? "dink" = some (grabDinkValue I))
    (hbase : locals.get? "gem" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabGemSourceSlot I) = gemOld)
    (hnew : gemNew = UInt256.sub gemOld (grabDinkWord I))
    (hguardNeg : grabDinkInt I ≤ 0 ∨ gemNew.toNat ≤ gemOld.toNat)
    (hguardPos : 0 ≤ grabDinkInt I ∨ gemOld.toNat ≤ gemNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v"))) (.var "dink"))
      (.ok
        { contract := contract,
          locals := locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat)) }
        evm) := by
  let locals' := locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (gemRef (.var "i") (.var "v"))) =
        .ok (.int (Int.ofNat gemOld.toNat)) := by
    rw [evalExpr_grab_gem_locals locals hsz196 hi hv hbase, hload]
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (grabDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [grabDinkValue] using hdink)
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256
          (.binary .sub (.storage (gemRef (.var "i") (.var "v"))) (.var "dink"))) =
        .ok (.int (Int.ofNat gemNew.toNat)) := by
    exact evalExpr_fold_wordWrapSub_ok hstorage hdinkEval
      (by simpa [hnew] using
        signedSubWrap gemOld (grabDinkWord I) (grabDinkInt I) (grabDinkInt_mod_word I))
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "gemNew") =
        .ok (.int (Int.ofNat gemNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdinkAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dink") =
        .ok (.int (grabDinkInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "dink" =
        some (.int (grabDinkInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [grabDinkValue] using hdink)
  have hiAfter : locals'.get? "i" = some (grabIValue I) := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "i" =
      some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hi
  have hvAfter : locals'.get? "v" = some (grabVValue I) := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "v" =
      some (grabVValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hv
  have hbaseAfter : locals'.get? "gem" = none := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "gem" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (gemRef (.var "i") (.var "v"))) =
        .ok (.int (Int.ofNat gemOld.toNat)) := by
    rw [evalExpr_grab_gem_locals locals' hsz196 hiAfter hvAfter hbaseAfter, hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dink") (.intLit 0))
          (.binary .le (.var "gemNew") (.storage (gemRef (.var "i") (.var "v"))))) =
        .ok (.bool true) :=
    evalSignedSubGuardNeg_true hdinkAfter hnewEval hstorageAfter hguardNeg
  have hguardPosEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dink") (.intLit 0))
          (.binary .ge (.var "gemNew") (.storage (gemRef (.var "i") (.var "v"))))) =
        .ok (.bool true) :=
    evalSignedSubGuardPos_true hdinkAfter hnewEval hstorageAfter hguardPos
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "gemNew" (some uint256)
        (wordWrap256
          (.binary .sub (.storage (gemRef (.var "i") (.var "v"))) (.var "dink"))),
      .require
        (eitherExpr (.binary .le (.var "dink") (.intLit 0))
          (.binary .le (.var "gemNew") (.storage (gemRef (.var "i") (.var "v"))))),
      .require
        (eitherExpr (.binary .ge (.var "dink") (.intLit 0))
          (.binary .ge (.var "gemNew") (.storage (gemRef (.var "i") (.var "v"))))) ]
    (.ok { contract := contract, locals := locals' } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNegEval) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguardPosEval) ExecBlock.nil

theorem execCheckedSubSignedRevertGuardNeg {evm : EVM.State} {locals : Store}
    {x y : Expr} {name : Ident} {old new : UInt256} {subtrahendInt : Int}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int subtrahendInt))
    (hwrap :
      (Int.ofNat old.toNat - subtrahendInt) % (Int.ofNat EVM.wordModulus) =
        Int.ofNat new.toNat)
    (hyAfter :
      evalExpr? config
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) } evm y =
      .ok (.int subtrahendInt))
    (hxAfter :
      evalExpr? config
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (hcond : 0 < subtrahendInt ∧ old.toNat < new.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto name x y)
      .reverted := by
  let locals' := locals.insert name (.int (Int.ofNat new.toNat))
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256 (.binary .sub x y)) =
        .ok (.int (Int.ofNat new.toNat)) :=
    evalExpr_fold_wordWrapSub_ok hx hy hwrap
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var name) =
        .ok (.int (Int.ofNat new.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le y (.intLit 0)) (.binary .le (.var name) x)) =
        .ok (.bool false) :=
    evalSignedSubGuardNeg_false (by simpa [locals'] using hyAfter)
      hnewEval (by simpa [locals'] using hxAfter) hcond
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl name (some uint256) (wordWrap256 (.binary .sub x y)),
      .require (eitherExpr (.binary .le y (.intLit 0)) (.binary .le (.var name) x)),
      .require (eitherExpr (.binary .ge y (.intLit 0)) (.binary .ge (.var name) x)) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguardNegEval)

theorem execCheckedSubSignedRevertGuardPos {evm : EVM.State} {locals : Store}
    {x y : Expr} {name : Ident} {old new : UInt256} {subtrahendInt : Int}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int subtrahendInt))
    (hwrap :
      (Int.ofNat old.toNat - subtrahendInt) % (Int.ofNat EVM.wordModulus) =
        Int.ofNat new.toNat)
    (hyAfter :
      evalExpr? config
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) } evm y =
      .ok (.int subtrahendInt))
    (hxAfter :
      evalExpr? config
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (hguardNeg :
      evalExpr? config
        { contract := contract, locals := locals.insert name (.int (Int.ofNat new.toNat)) } evm
        (eitherExpr (.binary .le y (.intLit 0)) (.binary .le (.var name) x)) =
      .ok (.bool true))
    (hcond : subtrahendInt < 0 ∧ new.toNat < old.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto name x y)
      .reverted := by
  let locals' := locals.insert name (.int (Int.ofNat new.toNat))
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256 (.binary .sub x y)) =
        .ok (.int (Int.ofNat new.toNat)) :=
    evalExpr_fold_wordWrapSub_ok hx hy hwrap
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var name) =
        .ok (.int (Int.ofNat new.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hguardPosEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge y (.intLit 0)) (.binary .ge (.var name) x)) =
        .ok (.bool false) :=
    evalSignedSubGuardPos_false (by simpa [locals'] using hyAfter)
      hnewEval (by simpa [locals'] using hxAfter) hcond
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl name (some uint256) (wordWrap256 (.binary .sub x y)),
      .require (eitherExpr (.binary .le y (.intLit 0)) (.binary .le (.var name) x)),
      .require (eitherExpr (.binary .ge y (.intLit 0)) (.binary .ge (.var name) x)) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals'] using hguardNeg)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguardPosEval)

theorem execGrabGemSubCheckedRevertGuardNeg {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (gemOld gemNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hv : locals.get? "v" = some (grabVValue I))
    (hdink : locals.get? "dink" = some (grabDinkValue I))
    (hbase : locals.get? "gem" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabGemSourceSlot I) = gemOld)
    (hnew : gemNew = UInt256.sub gemOld (grabDinkWord I))
    (hfail :
      ¬ (UInt256.sgt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt gemNew gemOld = ⟨0⟩)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v"))) (.var "dink"))
      .reverted := by
  let locals' := locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (gemRef (.var "i") (.var "v"))) =
        .ok (.int (Int.ofNat gemOld.toNat)) := by
    rw [evalExpr_grab_gem_locals locals hsz196 hi hv hbase, hload]
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (grabDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [grabDinkValue] using hdink)
  have hdinkAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dink") =
        .ok (.int (grabDinkInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "dink" =
        some (.int (grabDinkInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [grabDinkValue] using hdink)
  have hiAfter : locals'.get? "i" = some (grabIValue I) := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "i" =
      some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hi
  have hvAfter : locals'.get? "v" = some (grabVValue I) := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "v" =
      some (grabVValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hv
  have hbaseAfter : locals'.get? "gem" = none := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "gem" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (gemRef (.var "i") (.var "v"))) =
        .ok (.int (Int.ofNat gemOld.toNat)) := by
    rw [evalExpr_grab_gem_locals locals' hsz196 hiAfter hvAfter hbaseAfter, hload]
  exact execCheckedSubSignedRevertGuardNeg
    (x := .storage (gemRef (.var "i") (.var "v"))) (y := .var "dink")
    (name := "gemNew") hstorage hdinkEval
    (by simpa [hnew] using
      signedSubWrap gemOld (grabDinkWord I) (grabDinkInt I) (grabDinkInt_mod_word I))
    (by simpa [locals'] using hdinkAfter)
    (by simpa [locals'] using hstorageAfter)
    (grabDinkSubGuardNegFailCond hfail)

theorem execGrabGemSubCheckedRevertGuardPos {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (gemOld gemNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hv : locals.get? "v" = some (grabVValue I))
    (hdink : locals.get? "dink" = some (grabDinkValue I))
    (hbase : locals.get? "gem" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabGemSourceSlot I) = gemOld)
    (hnew : gemNew = UInt256.sub gemOld (grabDinkWord I))
    (hguardNeg :
      UInt256.sgt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt gemNew gemOld = ⟨0⟩)
    (hfail :
      ¬ (UInt256.slt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt gemNew gemOld = ⟨0⟩)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v"))) (.var "dink"))
      .reverted := by
  let locals' := locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (gemRef (.var "i") (.var "v"))) =
        .ok (.int (Int.ofNat gemOld.toNat)) := by
    rw [evalExpr_grab_gem_locals locals hsz196 hi hv hbase, hload]
  have hdinkEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dink") =
        .ok (.int (grabDinkInt I)) :=
    vatEvalExpr_varInt (by simpa [grabDinkValue] using hdink)
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "gemNew") =
        .ok (.int (Int.ofNat gemNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdinkAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dink") =
        .ok (.int (grabDinkInt I)) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "dink" =
        some (.int (grabDinkInt I))
      rw [store_get_ne _ _ (by native_decide)]
      simpa [grabDinkValue] using hdink)
  have hiAfter : locals'.get? "i" = some (grabIValue I) := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "i" =
      some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hi
  have hvAfter : locals'.get? "v" = some (grabVValue I) := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "v" =
      some (grabVValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hv
  have hbaseAfter : locals'.get? "gem" = none := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "gem" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (gemRef (.var "i") (.var "v"))) =
        .ok (.int (Int.ofNat gemOld.toNat)) := by
    rw [evalExpr_grab_gem_locals locals' hsz196 hiAfter hvAfter hbaseAfter, hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dink") (.intLit 0))
          (.binary .le (.var "gemNew") (.storage (gemRef (.var "i") (.var "v"))))) =
        .ok (.bool true) :=
    evalSignedSubGuardNeg_true hdinkAfter hnewEval hstorageAfter
      (grabDinkSubGuardNegCond hguardNeg)
  exact execCheckedSubSignedRevertGuardPos
    (x := .storage (gemRef (.var "i") (.var "v"))) (y := .var "dink")
    (name := "gemNew") hstorage hdinkEval
    (by simpa [hnew] using
      signedSubWrap gemOld (grabDinkWord I) (grabDinkInt I) (grabDinkInt_mod_word I))
    (by simpa [locals'] using hdinkAfter)
    (by simpa [locals'] using hstorageAfter)
    (by simpa [locals'] using hguardNegEval)
    (grabDinkSubGuardPosFailCond hfail)

theorem execGrabSinSubCheckedOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (sinOld sinNew dtabWord : UInt256) (dtab : Int)
    (hw : locals.get? "w" = some (grabWValue I))
    (hdtab : locals.get? "dtab" = some (.int dtab))
    (hbase : locals.get? "sin" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabSinSourceSlot I) = sinOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : sinNew = UInt256.sub sinOld dtabWord)
    (hguardNeg : dtab ≤ 0 ∨ sinNew.toNat ≤ sinOld.toNat)
    (hguardPos : 0 ≤ dtab ∨ sinOld.toNat ≤ sinNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "sinNew" (.storage (sinRef (.var "w"))) (.var "dtab"))
      (.ok
        { contract := contract,
          locals := locals.insert "sinNew" (.int (Int.ofNat sinNew.toNat)) }
        evm) := by
  let locals' := locals.insert "sinNew" (.int (Int.ofNat sinNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (sinRef (.var "w"))) =
        .ok (.int (Int.ofNat sinOld.toNat)) := by
    rw [evalExpr_grab_sin_locals locals hw hbase, hload]
  have hdtabEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dtab") =
        .ok (.int dtab) :=
    vatEvalExpr_varInt hdtab
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256 (.binary .sub (.storage (sinRef (.var "w"))) (.var "dtab"))) =
        .ok (.int (Int.ofNat sinNew.toNat)) := by
    exact evalExpr_fold_wordWrapSub_ok hstorage hdtabEval
      (by simpa [hnew] using signedSubWrap sinOld dtabWord dtab hdtabMod)
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "sinNew") =
        .ok (.int (Int.ofNat sinNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdtabAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dtab") =
        .ok (.int dtab) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "sinNew" (.int (Int.ofNat sinNew.toNat))).get? "dtab" =
        some (.int dtab)
      rw [store_get_ne _ _ (by native_decide)]
      exact hdtab)
  have hwAfter : locals'.get? "w" = some (grabWValue I) := by
    change (locals.insert "sinNew" (.int (Int.ofNat sinNew.toNat))).get? "w" =
      some (grabWValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hw
  have hbaseAfter : locals'.get? "sin" = none := by
    change (locals.insert "sinNew" (.int (Int.ofNat sinNew.toNat))).get? "sin" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (sinRef (.var "w"))) =
        .ok (.int (Int.ofNat sinOld.toNat)) := by
    rw [evalExpr_grab_sin_locals locals' hwAfter hbaseAfter, hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dtab") (.intLit 0))
          (.binary .le (.var "sinNew") (.storage (sinRef (.var "w"))))) =
        .ok (.bool true) :=
    evalSignedSubGuardNeg_true hdtabAfter hnewEval hstorageAfter hguardNeg
  have hguardPosEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dtab") (.intLit 0))
          (.binary .ge (.var "sinNew") (.storage (sinRef (.var "w"))))) =
        .ok (.bool true) :=
    evalSignedSubGuardPos_true hdtabAfter hnewEval hstorageAfter hguardPos
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "sinNew" (some uint256)
        (wordWrap256 (.binary .sub (.storage (sinRef (.var "w"))) (.var "dtab"))),
      .require
        (eitherExpr (.binary .le (.var "dtab") (.intLit 0))
          (.binary .le (.var "sinNew") (.storage (sinRef (.var "w"))))),
      .require
        (eitherExpr (.binary .ge (.var "dtab") (.intLit 0))
          (.binary .ge (.var "sinNew") (.storage (sinRef (.var "w"))))) ]
    (.ok { contract := contract, locals := locals' } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNegEval) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguardPosEval) ExecBlock.nil

theorem execGrabSinSubCheckedRevertGuardNeg {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (sinOld sinNew dtabWord : UInt256) (dtab : Int)
    (hw : locals.get? "w" = some (grabWValue I))
    (hdtab : locals.get? "dtab" = some (.int dtab))
    (hbase : locals.get? "sin" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabSinSourceSlot I) = sinOld)
    (hdtabLo : -((2 : Int) ^ 255) ≤ dtab)
    (hdtabHi : dtab < (2 : Int) ^ 255)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : sinNew = UInt256.sub sinOld dtabWord)
    (hfail :
      ¬ (UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt sinNew sinOld = ⟨0⟩)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "sinNew" (.storage (sinRef (.var "w"))) (.var "dtab"))
      .reverted := by
  let locals' := locals.insert "sinNew" (.int (Int.ofNat sinNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (sinRef (.var "w"))) =
        .ok (.int (Int.ofNat sinOld.toNat)) := by
    rw [evalExpr_grab_sin_locals locals hw hbase, hload]
  have hdtabEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dtab") =
        .ok (.int dtab) :=
    vatEvalExpr_varInt hdtab
  have hdtabAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dtab") =
        .ok (.int dtab) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "sinNew" (.int (Int.ofNat sinNew.toNat))).get? "dtab" =
        some (.int dtab)
      rw [store_get_ne _ _ (by native_decide)]
      exact hdtab)
  have hwAfter : locals'.get? "w" = some (grabWValue I) := by
    change (locals.insert "sinNew" (.int (Int.ofNat sinNew.toNat))).get? "w" =
      some (grabWValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hw
  have hbaseAfter : locals'.get? "sin" = none := by
    change (locals.insert "sinNew" (.int (Int.ofNat sinNew.toNat))).get? "sin" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (sinRef (.var "w"))) =
        .ok (.int (Int.ofNat sinOld.toNat)) := by
    rw [evalExpr_grab_sin_locals locals' hwAfter hbaseAfter, hload]
  exact execCheckedSubSignedRevertGuardNeg
    (x := .storage (sinRef (.var "w"))) (y := .var "dtab")
    (name := "sinNew") hstorage hdtabEval
    (by simpa [hnew] using signedSubWrap sinOld dtabWord dtab hdtabMod)
    (by simpa [locals'] using hdtabAfter)
    (by simpa [locals'] using hstorageAfter)
    (grabDtabSubGuardNegFailCond hdtabLo hdtabHi hdtabMod hfail)

theorem execGrabSinSubCheckedRevertGuardPos {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (sinOld sinNew dtabWord : UInt256) (dtab : Int)
    (hw : locals.get? "w" = some (grabWValue I))
    (hdtab : locals.get? "dtab" = some (.int dtab))
    (hbase : locals.get? "sin" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabSinSourceSlot I) = sinOld)
    (hdtabLo : -((2 : Int) ^ 255) ≤ dtab)
    (hdtabHi : dtab < (2 : Int) ^ 255)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : sinNew = UInt256.sub sinOld dtabWord)
    (hguardNeg :
      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt sinNew sinOld = ⟨0⟩)
    (hfail :
      ¬ (UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt sinNew sinOld = ⟨0⟩)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "sinNew" (.storage (sinRef (.var "w"))) (.var "dtab"))
      .reverted := by
  let locals' := locals.insert "sinNew" (.int (Int.ofNat sinNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (sinRef (.var "w"))) =
        .ok (.int (Int.ofNat sinOld.toNat)) := by
    rw [evalExpr_grab_sin_locals locals hw hbase, hload]
  have hdtabEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dtab") =
        .ok (.int dtab) :=
    vatEvalExpr_varInt hdtab
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "sinNew") =
        .ok (.int (Int.ofNat sinNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdtabAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dtab") =
        .ok (.int dtab) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "sinNew" (.int (Int.ofNat sinNew.toNat))).get? "dtab" =
        some (.int dtab)
      rw [store_get_ne _ _ (by native_decide)]
      exact hdtab)
  have hwAfter : locals'.get? "w" = some (grabWValue I) := by
    change (locals.insert "sinNew" (.int (Int.ofNat sinNew.toNat))).get? "w" =
      some (grabWValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hw
  have hbaseAfter : locals'.get? "sin" = none := by
    change (locals.insert "sinNew" (.int (Int.ofNat sinNew.toNat))).get? "sin" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm
        (.storage (sinRef (.var "w"))) =
        .ok (.int (Int.ofNat sinOld.toNat)) := by
    rw [evalExpr_grab_sin_locals locals' hwAfter hbaseAfter, hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dtab") (.intLit 0))
          (.binary .le (.var "sinNew") (.storage (sinRef (.var "w"))))) =
        .ok (.bool true) :=
    evalSignedSubGuardNeg_true hdtabAfter hnewEval hstorageAfter
      (grabDtabSubGuardNegCond hdtabLo hdtabHi hdtabMod hguardNeg)
  exact execCheckedSubSignedRevertGuardPos
    (x := .storage (sinRef (.var "w"))) (y := .var "dtab")
    (name := "sinNew") hstorage hdtabEval
    (by simpa [hnew] using signedSubWrap sinOld dtabWord dtab hdtabMod)
    (by simpa [locals'] using hdtabAfter)
    (by simpa [locals'] using hstorageAfter)
    (by simpa [locals'] using hguardNegEval)
    (grabDtabSubGuardPosFailCond hdtabLo hdtabHi hdtabMod hfail)

theorem execGrabViceSubCheckedOk {evm : EVM.State}
    (locals : Store) (viceOld viceNew dtabWord : UInt256) (dtab : Int)
    (hdtab : locals.get? "dtab" = some (.int dtab))
    (hbase : locals.get? "vice" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner grabViceSourceSlot = viceOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : viceNew = UInt256.sub viceOld dtabWord)
    (hguardNeg : dtab ≤ 0 ∨ viceNew.toNat ≤ viceOld.toNat)
    (hguardPos : 0 ≤ dtab ∨ viceOld.toNat ≤ viceNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "viceNew" (.storage viceRef) (.var "dtab"))
      (.ok
        { contract := contract,
          locals := locals.insert "viceNew" (.int (Int.ofNat viceNew.toNat)) }
        evm) := by
  let locals' := locals.insert "viceNew" (.int (Int.ofNat viceNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm (.storage viceRef) =
        .ok (.int (Int.ofNat viceOld.toNat)) := by
    rw [evalExpr_grab_vice_locals locals hbase, hload]
  have hdtabEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dtab") =
        .ok (.int dtab) :=
    vatEvalExpr_varInt hdtab
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm
        (wordWrap256 (.binary .sub (.storage viceRef) (.var "dtab"))) =
        .ok (.int (Int.ofNat viceNew.toNat)) := by
    exact evalExpr_fold_wordWrapSub_ok hstorage hdtabEval
      (by simpa [hnew] using signedSubWrap viceOld dtabWord dtab hdtabMod)
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "viceNew") =
        .ok (.int (Int.ofNat viceNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdtabAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dtab") =
        .ok (.int dtab) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "viceNew" (.int (Int.ofNat viceNew.toNat))).get? "dtab" =
        some (.int dtab)
      rw [store_get_ne _ _ (by native_decide)]
      exact hdtab)
  have hbaseAfter : locals'.get? "vice" = none := by
    change (locals.insert "viceNew" (.int (Int.ofNat viceNew.toNat))).get? "vice" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.storage viceRef) =
        .ok (.int (Int.ofNat viceOld.toNat)) := by
    rw [evalExpr_grab_vice_locals locals' hbaseAfter, hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dtab") (.intLit 0))
          (.binary .le (.var "viceNew") (.storage viceRef))) =
        .ok (.bool true) :=
    evalSignedSubGuardNeg_true hdtabAfter hnewEval hstorageAfter hguardNeg
  have hguardPosEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .ge (.var "dtab") (.intLit 0))
          (.binary .ge (.var "viceNew") (.storage viceRef))) =
        .ok (.bool true) :=
    evalSignedSubGuardPos_true hdtabAfter hnewEval hstorageAfter hguardPos
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .letDecl "viceNew" (some uint256)
        (wordWrap256 (.binary .sub (.storage viceRef) (.var "dtab"))),
      .require
        (eitherExpr (.binary .le (.var "dtab") (.intLit 0))
          (.binary .le (.var "viceNew") (.storage viceRef))),
      .require
        (eitherExpr (.binary .ge (.var "dtab") (.intLit 0))
          (.binary .ge (.var "viceNew") (.storage viceRef))) ]
    (.ok { contract := contract, locals := locals' } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNegEval) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguardPosEval) ExecBlock.nil

theorem execGrabViceSubCheckedRevertGuardNeg {evm : EVM.State}
    (locals : Store) (viceOld viceNew dtabWord : UInt256) (dtab : Int)
    (hdtab : locals.get? "dtab" = some (.int dtab))
    (hbase : locals.get? "vice" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner grabViceSourceSlot = viceOld)
    (hdtabLo : -((2 : Int) ^ 255) ≤ dtab)
    (hdtabHi : dtab < (2 : Int) ^ 255)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : viceNew = UInt256.sub viceOld dtabWord)
    (hfail :
      ¬ (UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt viceNew viceOld = ⟨0⟩)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "viceNew" (.storage viceRef) (.var "dtab"))
      .reverted := by
  let locals' := locals.insert "viceNew" (.int (Int.ofNat viceNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm (.storage viceRef) =
        .ok (.int (Int.ofNat viceOld.toNat)) := by
    rw [evalExpr_grab_vice_locals locals hbase, hload]
  have hdtabEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dtab") =
        .ok (.int dtab) :=
    vatEvalExpr_varInt hdtab
  have hdtabAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dtab") =
        .ok (.int dtab) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "viceNew" (.int (Int.ofNat viceNew.toNat))).get? "dtab" =
        some (.int dtab)
      rw [store_get_ne _ _ (by native_decide)]
      exact hdtab)
  have hbaseAfter : locals'.get? "vice" = none := by
    change (locals.insert "viceNew" (.int (Int.ofNat viceNew.toNat))).get? "vice" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.storage viceRef) =
        .ok (.int (Int.ofNat viceOld.toNat)) := by
    rw [evalExpr_grab_vice_locals locals' hbaseAfter, hload]
  exact execCheckedSubSignedRevertGuardNeg
    (x := .storage viceRef) (y := .var "dtab")
    (name := "viceNew") hstorage hdtabEval
    (by simpa [hnew] using signedSubWrap viceOld dtabWord dtab hdtabMod)
    (by simpa [locals'] using hdtabAfter)
    (by simpa [locals'] using hstorageAfter)
    (grabDtabSubGuardNegFailCond hdtabLo hdtabHi hdtabMod hfail)

theorem execGrabViceSubCheckedRevertGuardPos {evm : EVM.State}
    (locals : Store) (viceOld viceNew dtabWord : UInt256) (dtab : Int)
    (hdtab : locals.get? "dtab" = some (.int dtab))
    (hbase : locals.get? "vice" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner grabViceSourceSlot = viceOld)
    (hdtabLo : -((2 : Int) ^ 255) ≤ dtab)
    (hdtabHi : dtab < (2 : Int) ^ 255)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : viceNew = UInt256.sub viceOld dtabWord)
    (hguardNeg :
      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt viceNew viceOld = ⟨0⟩)
    (hfail :
      ¬ (UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt viceNew viceOld = ⟨0⟩)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "viceNew" (.storage viceRef) (.var "dtab"))
      .reverted := by
  let locals' := locals.insert "viceNew" (.int (Int.ofNat viceNew.toNat))
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm (.storage viceRef) =
        .ok (.int (Int.ofNat viceOld.toNat)) := by
    rw [evalExpr_grab_vice_locals locals hbase, hload]
  have hdtabEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "dtab") =
        .ok (.int dtab) :=
    vatEvalExpr_varInt hdtab
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "viceNew") =
        .ok (.int (Int.ofNat viceNew.toNat)) := by
    exact vatEvalExpr_varUInt256 (by simp [locals'])
  have hdtabAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "dtab") =
        .ok (.int dtab) := by
    exact vatEvalExpr_varInt (by
      change (locals.insert "viceNew" (.int (Int.ofNat viceNew.toNat))).get? "dtab" =
        some (.int dtab)
      rw [store_get_ne _ _ (by native_decide)]
      exact hdtab)
  have hbaseAfter : locals'.get? "vice" = none := by
    change (locals.insert "viceNew" (.int (Int.ofNat viceNew.toNat))).get? "vice" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hstorageAfter :
      evalExpr? config { contract := contract, locals := locals' } evm (.storage viceRef) =
        .ok (.int (Int.ofNat viceOld.toNat)) := by
    rw [evalExpr_grab_vice_locals locals' hbaseAfter, hload]
  have hguardNegEval :
      evalExpr? config { contract := contract, locals := locals' } evm
        (eitherExpr (.binary .le (.var "dtab") (.intLit 0))
          (.binary .le (.var "viceNew") (.storage viceRef))) =
        .ok (.bool true) :=
    evalSignedSubGuardNeg_true hdtabAfter hnewEval hstorageAfter
      (grabDtabSubGuardNegCond hdtabLo hdtabHi hdtabMod hguardNeg)
  exact execCheckedSubSignedRevertGuardPos
    (x := .storage viceRef) (y := .var "dtab")
    (name := "viceNew") hstorage hdtabEval
    (by simpa [hnew] using signedSubWrap viceOld dtabWord dtab hdtabMod)
    (by simpa [locals'] using hdtabAfter)
    (by simpa [locals'] using hstorageAfter)
    (by simpa [locals'] using hguardNegEval)
    (grabDtabSubGuardPosFailCond hdtabLo hdtabHi hdtabMod hfail)

theorem execGrabUrnArtUpdateOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (urnArtOld urnArtNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hu : locals.get? "u" = some (grabUValue I))
    (hdart : locals.get? "dart" = some (grabDartValue I))
    (hbase : locals.get? "urns" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabUrnArtSourceSlot I) = urnArtOld)
    (hnew : urnArtNew = grabDartWord I + urnArtOld)
    (hguardNeg : 0 ≤ grabDartInt I ∨ urnArtNew.toNat ≤ urnArtOld.toNat)
    (hguardPos : grabDartInt I ≤ 0 ∨ urnArtOld.toNat ≤ urnArtNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "urnArtNew" (.storage (urnsF (.var "i") (.var "u") "art"))
        (.var "dart") ++
        [ .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew") ])
      (.ok
        { contract := contract,
          locals := locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat)) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (grabUrnArtSourceSlot I) urnArtNew)) := by
  let locals' := locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (grabUrnArtSourceSlot I) urnArtNew
  have hchecked := execGrabUrnArtCheckedOk (evm := evm) (I := I) locals
    urnArtOld urnArtNew hsz196 hi hu hdart hbase hload hnew hguardNeg hguardPos
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "urnArtNew") =
        .ok (.int (Int.ofNat urnArtNew.toNat)) :=
    vatEvalExpr_varUInt256 (by simp [locals'])
  have hi' : locals'.get? "i" = some (grabIValue I) := by
    change (locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "i" =
      some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hi
  have hu' : locals'.get? "u" = some (grabUValue I) := by
    change (locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "u" =
      some (grabUValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hu
  have hbase' : locals'.get? "urns" = none := by
    change (locals.insert "urnArtNew" (.int (Int.ofNat urnArtNew.toNat))).get? "urns" =
      none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals' } evm .storage
        (urnsF (.var "i") (.var "u") "art") (.int (Int.ofNat urnArtNew.toNat)) =
        .ok ({ contract := contract, locals := locals' }, evm') := by
    simpa [evm'] using
      assignStorageRef_grab_urn_art evm I locals' urnArtNew hsz196 hi' hu' hbase'
  have hassignBlock :
      ExecBlock config { contract := contract, locals := locals' } evm
        [ .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew") ]
        (.ok { contract := contract, locals := locals' } evm') :=
    ExecBlock.consNormal (ExecStmt.assign hnewEval hassign) ExecBlock.nil
  exact.execBlock_append hchecked hassignBlock

theorem execGrabIlkArtUpdateOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (ilkArtOld ilkArtNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hdart : locals.get? "dart" = some (grabDartValue I))
    (hbase : locals.get? "ilks" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabIlkArtSourceSlot I) = ilkArtOld)
    (hnew : ilkArtNew = grabDartWord I + ilkArtOld)
    (hguardNeg : 0 ≤ grabDartInt I ∨ ilkArtNew.toNat ≤ ilkArtOld.toNat)
    (hguardPos : grabDartInt I ≤ 0 ∨ ilkArtOld.toNat ≤ ilkArtNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedAddSignedInto "ilkArtNew" (.storage (ilksF (.var "i") "Art"))
        (.var "dart") ++
        [ .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew") ])
      (.ok
        { contract := contract,
          locals := locals.insert "ilkArtNew" (.int (Int.ofNat ilkArtNew.toNat)) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (grabIlkArtSourceSlot I) ilkArtNew)) := by
  let locals' := locals.insert "ilkArtNew" (.int (Int.ofNat ilkArtNew.toNat))
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (grabIlkArtSourceSlot I) ilkArtNew
  have hchecked := execGrabIlkArtCheckedOk (evm := evm) (I := I) locals
    ilkArtOld ilkArtNew hsz196 hi hdart hbase hload hnew hguardNeg hguardPos
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "ilkArtNew") =
        .ok (.int (Int.ofNat ilkArtNew.toNat)) :=
    vatEvalExpr_varUInt256 (by simp [locals'])
  have hi' : locals'.get? "i" = some (grabIValue I) := by
    change (locals.insert "ilkArtNew" (.int (Int.ofNat ilkArtNew.toNat))).get? "i" =
      some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hi
  have hbase' : locals'.get? "ilks" = none := by
    change (locals.insert "ilkArtNew" (.int (Int.ofNat ilkArtNew.toNat))).get? "ilks" =
      none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals' } evm .storage
        (ilksF (.var "i") "Art") (.int (Int.ofNat ilkArtNew.toNat)) =
        .ok ({ contract := contract, locals := locals' }, evm') := by
    simpa [evm'] using
      assignStorageRef_grab_ilk_art evm I locals' ilkArtNew hsz196 hi' hbase'
  have hassignBlock :
      ExecBlock config { contract := contract, locals := locals' } evm
        [ .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew") ]
        (.ok { contract := contract, locals := locals' } evm') :=
    ExecBlock.consNormal (ExecStmt.assign hnewEval hassign) ExecBlock.nil
  exact.execBlock_append hchecked hassignBlock

theorem execGrabGemUpdateOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (gemOld gemNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hv : locals.get? "v" = some (grabVValue I))
    (hdink : locals.get? "dink" = some (grabDinkValue I))
    (hbase : locals.get? "gem" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabGemSourceSlot I) = gemOld)
    (hnew : gemNew = UInt256.sub gemOld (grabDinkWord I))
    (hguardNeg : grabDinkInt I ≤ 0 ∨ gemNew.toNat ≤ gemOld.toNat)
    (hguardPos : 0 ≤ grabDinkInt I ∨ gemOld.toNat ≤ gemNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
        [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ])
      (.ok
        { contract := contract,
          locals := locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat)) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (grabGemSourceSlot I) gemNew)) := by
  let locals' := locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (grabGemSourceSlot I) gemNew
  have hchecked := execGrabGemSubCheckedOk (evm := evm) (I := I) locals
    gemOld gemNew hsz196 hi hv hdink hbase hload hnew hguardNeg hguardPos
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "gemNew") =
        .ok (.int (Int.ofNat gemNew.toNat)) :=
    vatEvalExpr_varUInt256 (by simp [locals'])
  have hi' : locals'.get? "i" = some (grabIValue I) := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "i" =
      some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hi
  have hv' : locals'.get? "v" = some (grabVValue I) := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "v" =
      some (grabVValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hv
  have hbase' : locals'.get? "gem" = none := by
    change (locals.insert "gemNew" (.int (Int.ofNat gemNew.toNat))).get? "gem" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals' } evm .storage
        (gemRef (.var "i") (.var "v")) (.int (Int.ofNat gemNew.toNat)) =
        .ok ({ contract := contract, locals := locals' }, evm') := by
    simpa [evm'] using
      assignStorageRef_grab_gem evm I locals' gemNew hsz196 hi' hv' hbase'
  have hassignBlock :
      ExecBlock config { contract := contract, locals := locals' } evm
        [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ]
        (.ok { contract := contract, locals := locals' } evm') :=
    ExecBlock.consNormal (ExecStmt.assign hnewEval hassign) ExecBlock.nil
  exact.execBlock_append hchecked hassignBlock

theorem execGrabSinUpdateOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store) (sinOld sinNew dtabWord : UInt256) (dtab : Int)
    (hw : locals.get? "w" = some (grabWValue I))
    (hdtab : locals.get? "dtab" = some (.int dtab))
    (hbase : locals.get? "sin" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (grabSinSourceSlot I) = sinOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : sinNew = UInt256.sub sinOld dtabWord)
    (hguardNeg : dtab ≤ 0 ∨ sinNew.toNat ≤ sinOld.toNat)
    (hguardPos : 0 ≤ dtab ∨ sinOld.toNat ≤ sinNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "sinNew" (.storage (sinRef (.var "w"))) (.var "dtab") ++
        [ .assign .storage (sinRef (.var "w")) (.var "sinNew") ])
      (.ok
        { contract := contract,
          locals := locals.insert "sinNew" (.int (Int.ofNat sinNew.toNat)) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (grabSinSourceSlot I) sinNew)) := by
  let locals' := locals.insert "sinNew" (.int (Int.ofNat sinNew.toNat))
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (grabSinSourceSlot I) sinNew
  have hchecked := execGrabSinSubCheckedOk (evm := evm) (I := I) locals
    sinOld sinNew dtabWord dtab hw hdtab hbase hload hdtabMod hnew hguardNeg hguardPos
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "sinNew") =
        .ok (.int (Int.ofNat sinNew.toNat)) :=
    vatEvalExpr_varUInt256 (by simp [locals'])
  have hw' : locals'.get? "w" = some (grabWValue I) := by
    change (locals.insert "sinNew" (.int (Int.ofNat sinNew.toNat))).get? "w" =
      some (grabWValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hw
  have hbase' : locals'.get? "sin" = none := by
    change (locals.insert "sinNew" (.int (Int.ofNat sinNew.toNat))).get? "sin" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals' } evm .storage
        (sinRef (.var "w")) (.int (Int.ofNat sinNew.toNat)) =
        .ok ({ contract := contract, locals := locals' }, evm') := by
    simpa [evm'] using
      assignStorageRef_grab_sin evm I locals' sinNew hw' hbase'
  have hassignBlock :
      ExecBlock config { contract := contract, locals := locals' } evm
        [ .assign .storage (sinRef (.var "w")) (.var "sinNew") ]
        (.ok { contract := contract, locals := locals' } evm') :=
    ExecBlock.consNormal (ExecStmt.assign hnewEval hassign) ExecBlock.nil
  exact.execBlock_append hchecked hassignBlock

theorem execGrabViceUpdateOk {evm : EVM.State}
    (locals : Store) (viceOld viceNew dtabWord : UInt256) (dtab : Int)
    (hdtab : locals.get? "dtab" = some (.int dtab))
    (hbase : locals.get? "vice" = none)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner grabViceSourceSlot = viceOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hnew : viceNew = UInt256.sub viceOld dtabWord)
    (hguardNeg : dtab ≤ 0 ∨ viceNew.toNat ≤ viceOld.toNat)
    (hguardPos : 0 ≤ dtab ∨ viceOld.toNat ≤ viceNew.toNat) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "viceNew" (.storage viceRef) (.var "dtab") ++
        [ .assign .storage viceRef (.var "viceNew") ])
      (.ok
        { contract := contract,
          locals := locals.insert "viceNew" (.int (Int.ofNat viceNew.toNat)) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          grabViceSourceSlot viceNew)) := by
  let locals' := locals.insert "viceNew" (.int (Int.ofNat viceNew.toNat))
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner grabViceSourceSlot viceNew
  have hchecked := execGrabViceSubCheckedOk (evm := evm) locals
    viceOld viceNew dtabWord dtab hdtab hbase hload hdtabMod hnew hguardNeg hguardPos
  have hnewEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "viceNew") =
        .ok (.int (Int.ofNat viceNew.toNat)) :=
    vatEvalExpr_varUInt256 (by simp [locals'])
  have hbase' : locals'.get? "vice" = none := by
    change (locals.insert "viceNew" (.int (Int.ofNat viceNew.toNat))).get? "vice" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact hbase
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals' } evm .storage
        viceRef (.int (Int.ofNat viceNew.toNat)) =
        .ok ({ contract := contract, locals := locals' }, evm') := by
    simpa [evm'] using
      assignStorageRef_grab_vice evm locals' viceNew hbase'
  have hassignBlock :
      ExecBlock config { contract := contract, locals := locals' } evm
        [ .assign .storage viceRef (.var "viceNew") ]
        (.ok { contract := contract, locals := locals' } evm') :=
    ExecBlock.consNormal (ExecStmt.assign hnewEval hassign) ExecBlock.nil
  exact.execBlock_append hchecked hassignBlock

theorem execGrabFinalAssignmentsOk {evm : EVM.State} {I : ExecutionEnv}
    (locals : Store)
    (urnInkNew urnArtNew ilkArtNew gemNew sinNew viceNew : UInt256)
    (hsz196 : 196 ≤ I.calldata.size)
    (hi : locals.get? "i" = some (grabIValue I))
    (hu : locals.get? "u" = some (grabUValue I))
    (hv : locals.get? "v" = some (grabVValue I))
    (hw : locals.get? "w" = some (grabWValue I))
    (hurnInkNew : locals.get? "urnInkNew" =
      some (.int (Int.ofNat urnInkNew.toNat)))
    (hurnArtNew : locals.get? "urnArtNew" =
      some (.int (Int.ofNat urnArtNew.toNat)))
    (hilkArtNew : locals.get? "ilkArtNew" =
      some (.int (Int.ofNat ilkArtNew.toNat)))
    (hgemNew : locals.get? "gemNew" =
      some (.int (Int.ofNat gemNew.toNat)))
    (hsinNew : locals.get? "sinNew" =
      some (.int (Int.ofNat sinNew.toNat)))
    (hviceNew : locals.get? "viceNew" =
      some (.int (Int.ofNat viceNew.toNat)))
    (hurns : locals.get? "urns" = none)
    (hilks : locals.get? "ilks" = none)
    (hgem : locals.get? "gem" = none)
    (hsin : locals.get? "sin" = none)
    (hvice : locals.get? "vice" = none) :
    let evm1 := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (grabUrnInkSourceSlot I) urnInkNew
    let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
      (grabUrnArtSourceSlot I) urnArtNew
    let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
      (grabIlkArtSourceSlot I) ilkArtNew
    let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
      (grabGemSourceSlot I) gemNew
    let evm5 := Solm.EVM.storageStore evm4 evm4.executionEnv.codeOwner
      (grabSinSourceSlot I) sinNew
    let evm6 := Solm.EVM.storageStore evm5 evm5.executionEnv.codeOwner
      grabViceSourceSlot viceNew
    ExecBlock config { contract := contract, locals := locals } evm
      [ .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
        .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
        .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew"),
        .assign .storage (sinRef (.var "w")) (.var "sinNew"),
        .assign .storage viceRef (.var "viceNew") ]
      (.ok { contract := contract, locals := locals } evm6) := by
  intro evm1 evm2 evm3 evm4 evm5 evm6
  have hurnInkNewEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "urnInkNew") =
        .ok (.int (Int.ofNat urnInkNew.toNat)) :=
    vatEvalExpr_varUInt256 hurnInkNew
  have hassignUrnInk :
      assignStorageRef? config { contract := contract, locals := locals } evm .storage
        (urnsF (.var "i") (.var "u") "ink") (.int (Int.ofNat urnInkNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [evm1] using
      assignStorageRef_grab_urn_ink evm I locals urnInkNew hsz196 hi hu hurns
  have hurnArtNewEval :
      evalExpr? config { contract := contract, locals := locals } evm1 (.var "urnArtNew") =
        .ok (.int (Int.ofNat urnArtNew.toNat)) :=
    vatEvalExpr_varUInt256 hurnArtNew
  have hassignUrnArt :
      assignStorageRef? config { contract := contract, locals := locals } evm1 .storage
        (urnsF (.var "i") (.var "u") "art") (.int (Int.ofNat urnArtNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm2) := by
    simpa [evm2] using
      assignStorageRef_grab_urn_art evm1 I locals urnArtNew hsz196 hi hu hurns
  have hilkArtNewEval :
      evalExpr? config { contract := contract, locals := locals } evm2 (.var "ilkArtNew") =
        .ok (.int (Int.ofNat ilkArtNew.toNat)) :=
    vatEvalExpr_varUInt256 hilkArtNew
  have hassignIlkArt :
      assignStorageRef? config { contract := contract, locals := locals } evm2 .storage
        (ilksF (.var "i") "Art") (.int (Int.ofNat ilkArtNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm3) := by
    simpa [evm3] using
      assignStorageRef_grab_ilk_art evm2 I locals ilkArtNew hsz196 hi hilks
  have hgemNewEval :
      evalExpr? config { contract := contract, locals := locals } evm3 (.var "gemNew") =
        .ok (.int (Int.ofNat gemNew.toNat)) :=
    vatEvalExpr_varUInt256 hgemNew
  have hassignGem :
      assignStorageRef? config { contract := contract, locals := locals } evm3 .storage
        (gemRef (.var "i") (.var "v")) (.int (Int.ofNat gemNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm4) := by
    simpa [evm4] using
      assignStorageRef_grab_gem evm3 I locals gemNew hsz196 hi hv hgem
  have hsinNewEval :
      evalExpr? config { contract := contract, locals := locals } evm4 (.var "sinNew") =
        .ok (.int (Int.ofNat sinNew.toNat)) :=
    vatEvalExpr_varUInt256 hsinNew
  have hassignSin :
      assignStorageRef? config { contract := contract, locals := locals } evm4 .storage
        (sinRef (.var "w")) (.int (Int.ofNat sinNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm5) := by
    simpa [evm5] using
      assignStorageRef_grab_sin evm4 I locals sinNew hw hsin
  have hviceNewEval :
      evalExpr? config { contract := contract, locals := locals } evm5 (.var "viceNew") =
        .ok (.int (Int.ofNat viceNew.toNat)) :=
    vatEvalExpr_varUInt256 hviceNew
  have hassignVice :
      assignStorageRef? config { contract := contract, locals := locals } evm5 .storage
        viceRef (.int (Int.ofNat viceNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm6) := by
    simpa [evm6] using
      assignStorageRef_grab_vice evm5 locals viceNew hvice
  refine ExecBlock.consNormal (ExecStmt.assign hurnInkNewEval hassignUrnInk) ?_
  refine ExecBlock.consNormal (ExecStmt.assign hurnArtNewEval hassignUrnArt) ?_
  refine ExecBlock.consNormal (ExecStmt.assign hilkArtNewEval hassignIlkArt) ?_
  refine ExecBlock.consNormal (ExecStmt.assign hgemNewEval hassignGem) ?_
  refine ExecBlock.consNormal (ExecStmt.assign hsinNewEval hassignSin) ?_
  exact ExecBlock.consNormal (ExecStmt.assign hviceNewEval hassignVice) ExecBlock.nil

theorem grabStoreViceNew_get_i (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int)
    (gemNew sinNew viceNew : UInt256) :
    (grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew viceNew).get? "i" =
      some (grabIValue I) := by
  unfold grabStoreViceNew grabStoreSinNew grabStoreGemNew grabStoreDtab
    grabStoreIlkArtNew grabStoreUrnArtNew grabStoreUrnInkNew
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  exact grabStore_get_i I

theorem grabStoreViceNew_get_u (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int)
    (gemNew sinNew viceNew : UInt256) :
    (grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew viceNew).get? "u" =
      some (grabUValue I) := by
  unfold grabStoreViceNew grabStoreSinNew grabStoreGemNew grabStoreDtab
    grabStoreIlkArtNew grabStoreUrnArtNew grabStoreUrnInkNew
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  exact grabStore_get_u I

theorem grabStoreViceNew_get_v (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int)
    (gemNew sinNew viceNew : UInt256) :
    (grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew viceNew).get? "v" =
      some (grabVValue I) := by
  unfold grabStoreViceNew grabStoreSinNew grabStoreGemNew grabStoreDtab
    grabStoreIlkArtNew grabStoreUrnArtNew grabStoreUrnInkNew
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  exact grabStore_get_v I

theorem grabStoreViceNew_get_w (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int)
    (gemNew sinNew viceNew : UInt256) :
    (grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew viceNew).get? "w" =
      some (grabWValue I) := by
  unfold grabStoreViceNew grabStoreSinNew grabStoreGemNew grabStoreDtab
    grabStoreIlkArtNew grabStoreUrnArtNew grabStoreUrnInkNew
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  exact grabStore_get_w I

theorem grabStoreViceNew_get_urnInkNew (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int)
    (gemNew sinNew viceNew : UInt256) :
    (grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew viceNew).get?
      "urnInkNew" = some (.int (Int.ofNat urnInkNew.toNat)) := by
  unfold grabStoreViceNew grabStoreSinNew grabStoreGemNew grabStoreDtab
    grabStoreIlkArtNew grabStoreUrnArtNew
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  unfold grabStoreUrnInkNew
  rw [store_get_self]

theorem grabStoreViceNew_get_urnArtNew (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int)
    (gemNew sinNew viceNew : UInt256) :
    (grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew viceNew).get?
      "urnArtNew" = some (.int (Int.ofNat urnArtNew.toNat)) := by
  unfold grabStoreViceNew grabStoreSinNew grabStoreGemNew grabStoreDtab
    grabStoreIlkArtNew
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  unfold grabStoreUrnArtNew
  rw [store_get_self]

theorem grabStoreViceNew_get_ilkArtNew (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int)
    (gemNew sinNew viceNew : UInt256) :
    (grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew viceNew).get?
      "ilkArtNew" = some (.int (Int.ofNat ilkArtNew.toNat)) := by
  unfold grabStoreViceNew grabStoreSinNew grabStoreGemNew grabStoreDtab
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  unfold grabStoreIlkArtNew
  rw [store_get_self]

theorem grabStoreViceNew_get_gemNew (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int)
    (gemNew sinNew viceNew : UInt256) :
    (grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew viceNew).get?
      "gemNew" = some (.int (Int.ofNat gemNew.toNat)) := by
  unfold grabStoreViceNew grabStoreSinNew
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  unfold grabStoreGemNew
  rw [store_get_self]

theorem grabStoreViceNew_get_sinNew (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int)
    (gemNew sinNew viceNew : UInt256) :
    (grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew viceNew).get?
      "sinNew" = some (.int (Int.ofNat sinNew.toNat)) := by
  unfold grabStoreViceNew
  rw [store_get_ne _ _ (by native_decide)]
  unfold grabStoreSinNew
  rw [store_get_self]

theorem grabStoreViceNew_get_viceNew (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int)
    (gemNew sinNew viceNew : UInt256) :
    (grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew viceNew).get?
      "viceNew" = some (.int (Int.ofNat viceNew.toNat)) := by
  simp [grabStoreViceNew]

theorem grabStoreViceNew_urns (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int)
    (gemNew sinNew viceNew : UInt256) :
    (grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew viceNew).get?
      "urns" = none := by
  simp [grabStoreViceNew, grabStoreSinNew, grabStoreGemNew, grabStoreDtab,
    grabStoreIlkArtNew, grabStoreUrnArtNew, grabStoreUrnInkNew, grabStore]

theorem grabStoreViceNew_ilks (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int)
    (gemNew sinNew viceNew : UInt256) :
    (grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew viceNew).get?
      "ilks" = none := by
  simp [grabStoreViceNew, grabStoreSinNew, grabStoreGemNew, grabStoreDtab,
    grabStoreIlkArtNew, grabStoreUrnArtNew, grabStoreUrnInkNew, grabStore]

theorem grabStoreViceNew_gem (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int)
    (gemNew sinNew viceNew : UInt256) :
    (grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew viceNew).get?
      "gem" = none := by
  simp [grabStoreViceNew, grabStoreSinNew, grabStoreGemNew, grabStoreDtab,
    grabStoreIlkArtNew, grabStoreUrnArtNew, grabStoreUrnInkNew, grabStore]

theorem grabStoreViceNew_sin (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int)
    (gemNew sinNew viceNew : UInt256) :
    (grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew viceNew).get?
      "sin" = none := by
  simp [grabStoreViceNew, grabStoreSinNew, grabStoreGemNew, grabStoreDtab,
    grabStoreIlkArtNew, grabStoreUrnArtNew, grabStoreUrnInkNew, grabStore]

theorem grabStoreViceNew_vice (I : ExecutionEnv)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int)
    (gemNew sinNew viceNew : UInt256) :
    (grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew viceNew).get?
      "vice" = none := by
  simp [grabStoreViceNew, grabStoreSinNew, grabStoreGemNew, grabStoreDtab,
    grabStoreIlkArtNew, grabStoreUrnArtNew, grabStoreUrnInkNew, grabStore]

theorem grabStore_get_wards (I : ExecutionEnv) :
    (grabStore I).get? "wards" = none := by
  simp [grabStore]

set_option maxHeartbeats 0 in
theorem execGrabSourceOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwei : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hsz196 : 196 ≤ I.calldata.size)
    (urnInkOld urnInkNew urnArtOld urnArtNew ilkArtOld ilkArtNew rateOld : UInt256)
    (dtab : Int) (dtabWord gemOld gemNew sinOld sinNew viceOld viceNew : UInt256)
    (hloadUrnInk :
      Solm.EVM.storageLoad (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (grabUrnInkSourceSlot I) = urnInkOld)
    (hurnInkNew : urnInkNew = grabDinkWord I + urnInkOld)
    (hinkNeg : 0 ≤ grabDinkInt I ∨ urnInkNew.toNat ≤ urnInkOld.toNat)
    (hinkPos : grabDinkInt I ≤ 0 ∨ urnInkOld.toNat ≤ urnInkNew.toNat)
    (hloadUrnArt :
      let evm1 := grabSourceEvm1 cA gh bl σ σ₀ A I g urnInkNew
      Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner (grabUrnArtSourceSlot I) =
        urnArtOld)
    (hurnArtNew : urnArtNew = grabDartWord I + urnArtOld)
    (hurnArtNeg : 0 ≤ grabDartInt I ∨ urnArtNew.toNat ≤ urnArtOld.toNat)
    (hurnArtPos : grabDartInt I ≤ 0 ∨ urnArtOld.toNat ≤ urnArtNew.toNat)
    (hloadIlkArt :
      let evm2 := grabSourceEvm2 cA gh bl σ σ₀ A I g urnInkNew urnArtNew
      Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner (grabIlkArtSourceSlot I) =
        ilkArtOld)
    (hilkArtNew : ilkArtNew = grabDartWord I + ilkArtOld)
    (hilkArtNeg : 0 ≤ grabDartInt I ∨ ilkArtNew.toNat ≤ ilkArtOld.toNat)
    (hilkArtPos : grabDartInt I ≤ 0 ∨ ilkArtOld.toNat ≤ ilkArtNew.toNat)
    (hloadRate :
      let evm3 := grabSourceEvm3 cA gh bl σ σ₀ A I g urnInkNew urnArtNew ilkArtNew
      Solm.EVM.storageLoad evm3 evm3.executionEnv.codeOwner (grabIlkRateSourceSlot I) =
        rateOld)
    (hdtab : dtab = Int.ofNat rateOld.toNat * grabDartInt I)
    (hdtabLo : -((2 : Int) ^ 255) ≤ dtab)
    (hdtabHi : dtab < (2 : Int) ^ 255)
    (hguardMax :
      let evm3 := grabSourceEvm3 cA gh bl σ σ₀ A I g urnInkNew urnArtNew ilkArtNew
      evalExpr? config
        { contract := contract,
          locals :=
            (grabStoreIlkArtNew I urnInkNew urnArtNew ilkArtNew).insert "dtab" (.int dtab) }
        evm3
        (.binary .le (.storage (ilksF (.var "i") "rate")) (.intLit maxInt256)) =
        .ok (.bool true))
    (hguardMul :
      let evm3 := grabSourceEvm3 cA gh bl σ σ₀ A I g urnInkNew urnArtNew ilkArtNew
      evalExpr? config
        { contract := contract,
          locals :=
            (grabStoreIlkArtNew I urnInkNew urnArtNew ilkArtNew).insert "dtab" (.int dtab) }
        evm3
        (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
          (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
            (.storage (ilksF (.var "i") "rate")))) =
        .ok (.bool true))
    (hloadGem :
      let evm3 := grabSourceEvm3 cA gh bl σ σ₀ A I g urnInkNew urnArtNew ilkArtNew
      Solm.EVM.storageLoad evm3 evm3.executionEnv.codeOwner (grabGemSourceSlot I) =
        gemOld)
    (hgemNew : gemNew = UInt256.sub gemOld (grabDinkWord I))
    (hgemNeg : grabDinkInt I ≤ 0 ∨ gemNew.toNat ≤ gemOld.toNat)
    (hgemPos : 0 ≤ grabDinkInt I ∨ gemOld.toNat ≤ gemNew.toNat)
    (hloadSin :
      let evm4 := grabSourceEvm4 cA gh bl σ σ₀ A I g urnInkNew urnArtNew ilkArtNew
        gemNew
      Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner (grabSinSourceSlot I) =
        sinOld)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hsinNew : sinNew = UInt256.sub sinOld dtabWord)
    (hsinNeg : dtab ≤ 0 ∨ sinNew.toNat ≤ sinOld.toNat)
    (hsinPos : 0 ≤ dtab ∨ sinOld.toNat ≤ sinNew.toNat)
    (hloadVice :
      let evm5 := grabSourceEvm5 cA gh bl σ σ₀ A I g urnInkNew urnArtNew ilkArtNew
        gemNew sinNew
      Solm.EVM.storageLoad evm5 evm5.executionEnv.codeOwner grabViceSourceSlot = viceOld)
    (hviceNew : viceNew = UInt256.sub viceOld dtabWord)
    (hviceNeg : dtab ≤ 0 ∨ viceNew.toNat ≤ viceOld.toNat)
    (hvicePos : 0 ≤ dtab ∨ viceOld.toNat ≤ viceNew.toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
      (grabUrnInkSourceSlot I) urnInkNew
    let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
      (grabUrnArtSourceSlot I) urnArtNew
    let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
      (grabIlkArtSourceSlot I) ilkArtNew
    let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
      (grabGemSourceSlot I) gemNew
    let evm5 := Solm.EVM.storageStore evm4 evm4.executionEnv.codeOwner
      (grabSinSourceSlot I) sinNew
    let evm6 := Solm.EVM.storageStore evm5 evm5.executionEnv.codeOwner
      grabViceSourceSlot viceNew
    let finalLocals := grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew
      viceNew
    ExecTransitionBody config contract evm0 (grabStore I) grabTransition.body
      (.returned { contract := contract, locals := finalLocals } evm6 none) := by
  intro evm0 evm1 evm2 evm3 evm4 evm5 evm6 finalLocals
  have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := grabStore I)
    (grabStore_get_wards I) hauth
  have hprefix :
      ExecBlock config { contract := contract, locals := grabStore I } evm0
        (nonpayable ++ auth) (.ok { contract := contract, locals := grabStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := grabStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]
      (.ok { contract := contract, locals := grabStore I } evm0)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwei)
    exact ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ExecBlock.nil
  have hInkBlock :=
    execGrabUrnInkUpdateOk (evm := evm0) (I := I) (locals := grabStore I)
      urnInkOld urnInkNew hsz196 (grabStore_get_i I) (grabStore_get_u I)
      (grabStore_get_dink I) (grabStore_urns I) hloadUrnInk hurnInkNew hinkNeg hinkPos
  let localsInk := grabStoreUrnInkNew I urnInkNew
  have hArt_i : localsInk.get? "i" = some (grabIValue I) := by
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "i" =
      some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact grabStore_get_i I
  have hArt_u : localsInk.get? "u" = some (grabUValue I) := by
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "u" =
      some (grabUValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact grabStore_get_u I
  have hArt_dart : localsInk.get? "dart" = some (grabDartValue I) := by
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get?
      "dart" = some (grabDartValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact grabStore_get_dart I
  have hArt_urns : localsInk.get? "urns" = none := by
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get?
      "urns" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact grabStore_urns I
  have hArtBlock :=
    execGrabUrnArtUpdateOk (evm := evm1) (I := I) (locals := localsInk)
      urnArtOld urnArtNew hsz196 hArt_i hArt_u hArt_dart hArt_urns
      (by simpa [evm0, evm1] using hloadUrnArt) hurnArtNew hurnArtNeg hurnArtPos
  let localsArt := grabStoreUrnArtNew I urnInkNew urnArtNew
  have hIlk_i : localsArt.get? "i" = some (grabIValue I) := by
    change ((grabStoreUrnInkNew I urnInkNew).insert "urnArtNew"
      (.int (Int.ofNat urnArtNew.toNat))).get? "i" = some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hArt_i
  have hIlk_dart : localsArt.get? "dart" = some (grabDartValue I) := by
    change ((grabStoreUrnInkNew I urnInkNew).insert "urnArtNew"
      (.int (Int.ofNat urnArtNew.toNat))).get? "dart" = some (grabDartValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hArt_dart
  have hIlk_ilks : localsArt.get? "ilks" = none := by
    change ((grabStoreUrnInkNew I urnInkNew).insert "urnArtNew"
      (.int (Int.ofNat urnArtNew.toNat))).get? "ilks" = none
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get?
      "ilks" = none
    rw [store_get_ne _ _ (by native_decide)]
    simp [grabStore]
  have hIlkBlock :=
    execGrabIlkArtUpdateOk (evm := evm2) (I := I) (locals := localsArt)
      ilkArtOld ilkArtNew hsz196 hIlk_i hIlk_dart hIlk_ilks
      (by simpa [evm0, evm1, evm2] using hloadIlkArt)
      hilkArtNew hilkArtNeg hilkArtPos
  let localsIlk := grabStoreIlkArtNew I urnInkNew urnArtNew ilkArtNew
  have hDtab_i : localsIlk.get? "i" = some (grabIValue I) := by
    change ((grabStoreUrnArtNew I urnInkNew urnArtNew).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat))).get? "i" = some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hIlk_i
  have hDtab_dart : localsIlk.get? "dart" = some (grabDartValue I) := by
    change ((grabStoreUrnArtNew I urnInkNew urnArtNew).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat))).get? "dart" = some (grabDartValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hIlk_dart
  have hDtab_ilks : localsIlk.get? "ilks" = none := by
    change ((grabStoreUrnArtNew I urnInkNew urnArtNew).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat))).get? "ilks" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact hIlk_ilks
  have hDtabBlock :=
    execGrabDtabMulCheckedOk (evm := evm3) (I := I) (locals := localsIlk)
      rateOld dtab hsz196 hDtab_i hDtab_dart hDtab_ilks
      (by simpa [evm0, evm1, evm2, evm3] using hloadRate) hdtab hdtabLo hdtabHi
      (by simpa [localsIlk, grabStoreDtab] using hguardMax)
      (by simpa [localsIlk, grabStoreDtab] using hguardMul)
  let localsDtab := grabStoreDtab I urnInkNew urnArtNew ilkArtNew dtab
  have hGem_i : localsDtab.get? "i" = some (grabIValue I) := by
    change ((grabStoreIlkArtNew I urnInkNew urnArtNew ilkArtNew).insert "dtab"
      (.int dtab)).get? "i" = some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hDtab_i
  have hGem_v : localsDtab.get? "v" = some (grabVValue I) := by
    change ((grabStoreIlkArtNew I urnInkNew urnArtNew ilkArtNew).insert "dtab"
      (.int dtab)).get? "v" = some (grabVValue I)
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStoreUrnArtNew I urnInkNew urnArtNew).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat))).get? "v" = some (grabVValue I)
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStoreUrnInkNew I urnInkNew).insert "urnArtNew"
      (.int (Int.ofNat urnArtNew.toNat))).get? "v" = some (grabVValue I)
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get?
      "v" = some (grabVValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact grabStore_get_v I
  have hGem_dink : localsDtab.get? "dink" = some (grabDinkValue I) := by
    change ((grabStoreIlkArtNew I urnInkNew urnArtNew ilkArtNew).insert "dtab"
      (.int dtab)).get? "dink" = some (grabDinkValue I)
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStoreUrnArtNew I urnInkNew urnArtNew).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat))).get? "dink" = some (grabDinkValue I)
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStoreUrnInkNew I urnInkNew).insert "urnArtNew"
      (.int (Int.ofNat urnArtNew.toNat))).get? "dink" = some (grabDinkValue I)
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get?
      "dink" = some (grabDinkValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact grabStore_get_dink I
  have hGem_gem : localsDtab.get? "gem" = none := by
    change ((grabStoreIlkArtNew I urnInkNew urnArtNew ilkArtNew).insert "dtab"
      (.int dtab)).get? "gem" = none
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStoreUrnArtNew I urnInkNew urnArtNew).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat))).get? "gem" = none
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStoreUrnInkNew I urnInkNew).insert "urnArtNew"
      (.int (Int.ofNat urnArtNew.toNat))).get? "gem" = none
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get?
      "gem" = none
    rw [store_get_ne _ _ (by native_decide)]
    simp [grabStore]
  have hGemBlock :=
    execGrabGemUpdateOk (evm := evm3) (I := I) (locals := localsDtab)
      gemOld gemNew hsz196 hGem_i hGem_v hGem_dink hGem_gem
      (by simpa [evm0, evm1, evm2, evm3] using hloadGem) hgemNew
      hgemNeg hgemPos
  let localsGem := grabStoreGemNew I urnInkNew urnArtNew ilkArtNew dtab gemNew
  have hSin_w : localsGem.get? "w" = some (grabWValue I) := by
    unfold localsGem grabStoreGemNew
    rw [store_get_ne _ _ (by native_decide)]
    unfold grabStoreDtab
    rw [store_get_ne _ _ (by native_decide)]
    unfold grabStoreIlkArtNew
    rw [store_get_ne _ _ (by native_decide)]
    unfold grabStoreUrnArtNew
    rw [store_get_ne _ _ (by native_decide)]
    unfold grabStoreUrnInkNew
    rw [store_get_ne _ _ (by native_decide)]
    exact grabStore_get_w I
  have hSin_dtab : localsGem.get? "dtab" = some (.int dtab) := by
    unfold localsGem grabStoreGemNew
    rw [store_get_ne _ _ (by native_decide)]
    unfold grabStoreDtab
    rw [store_get_self]
  have hSin_sin : localsGem.get? "sin" = none := by
    change ((grabStoreDtab I urnInkNew urnArtNew ilkArtNew dtab).insert "gemNew"
      (.int (Int.ofNat gemNew.toNat))).get? "sin" = none
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStoreIlkArtNew I urnInkNew urnArtNew ilkArtNew).insert "dtab"
      (.int dtab)).get? "sin" = none
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStoreUrnArtNew I urnInkNew urnArtNew).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat))).get? "sin" = none
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStoreUrnInkNew I urnInkNew).insert "urnArtNew"
      (.int (Int.ofNat urnArtNew.toNat))).get? "sin" = none
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get?
      "sin" = none
    rw [store_get_ne _ _ (by native_decide)]
    simp [grabStore]
  have hSinBlock :=
    execGrabSinUpdateOk (evm := evm4) (I := I) (locals := localsGem)
      sinOld sinNew dtabWord dtab hSin_w hSin_dtab hSin_sin
      (by simpa [evm0, evm1, evm2, evm3, evm4] using hloadSin) hdtabMod hsinNew
      hsinNeg hsinPos
  let localsSin := grabStoreSinNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew
  have hVice_dtab : localsSin.get? "dtab" = some (.int dtab) := by
    unfold localsSin grabStoreSinNew
    rw [store_get_ne _ _ (by native_decide)]
    exact hSin_dtab
  have hVice_vice : localsSin.get? "vice" = none := by
    change ((grabStoreGemNew I urnInkNew urnArtNew ilkArtNew dtab gemNew).insert "sinNew"
      (.int (Int.ofNat sinNew.toNat))).get? "vice" = none
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStoreDtab I urnInkNew urnArtNew ilkArtNew dtab).insert "gemNew"
      (.int (Int.ofNat gemNew.toNat))).get? "vice" = none
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStoreIlkArtNew I urnInkNew urnArtNew ilkArtNew).insert "dtab"
      (.int dtab)).get? "vice" = none
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStoreUrnArtNew I urnInkNew urnArtNew).insert "ilkArtNew"
      (.int (Int.ofNat ilkArtNew.toNat))).get? "vice" = none
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStoreUrnInkNew I urnInkNew).insert "urnArtNew"
      (.int (Int.ofNat urnArtNew.toNat))).get? "vice" = none
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get?
      "vice" = none
    rw [store_get_ne _ _ (by native_decide)]
    simp [grabStore]
  have hViceBlock :=
    execGrabViceUpdateOk (evm := evm5) (locals := localsSin)
      viceOld viceNew dtabWord dtab hVice_dtab hVice_vice
      (by simpa [evm0, evm1, evm2, evm3, evm4, evm5] using hloadVice) hdtabMod hviceNew
      hviceNeg hvicePos
  have h01 :=.execBlock_append hprefix hInkBlock
  have h02 :=.execBlock_append h01 hArtBlock
  have h03 :=.execBlock_append h02 hIlkBlock
  have h04 :=.execBlock_append h03 hDtabBlock
  have h05 :=.execBlock_append h04 hGemBlock
  have h06 :=.execBlock_append h05 hSinBlock
  have hblock :=.execBlock_append h06 hViceBlock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockOK hblock

theorem vatGrabSourceBodySuccessFromFinalValues
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwei : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hsz196 : 196 ≤ I.calldata.size)
    (dtab : Int) (dtabWord : UInt256)
    (hDtab :
      dtab =
        Int.ofNat (solcSlotWord (grabAfterIlkArt σ I) I (grabIlkRateSlot I)).toNat *
          grabDartInt I)
    (hdtabLo : -((2 : Int) ^ 255) ≤ dtab)
    (hdtabHi : dtab < (2 : Int) ^ 255)
    (hguardMax :
      let evm3 := grabSourceEvm3 cA gh bl σ σ₀ A I g
        (grabUrnInkNew σ I) (grabUrnArtNew σ I) (grabIlkArtNew σ I)
      evalExpr? config
        { contract := contract,
          locals :=
            (grabStoreIlkArtNew I (grabUrnInkNew σ I) (grabUrnArtNew σ I)
              (grabIlkArtNew σ I)).insert "dtab" (.int dtab) }
        evm3
        (.binary .le (.storage (ilksF (.var "i") "rate")) (.intLit maxInt256)) =
        .ok (.bool true))
    (hguardMul :
      let evm3 := grabSourceEvm3 cA gh bl σ σ₀ A I g
        (grabUrnInkNew σ I) (grabUrnArtNew σ I) (grabIlkArtNew σ I)
      evalExpr? config
        { contract := contract,
          locals :=
            (grabStoreIlkArtNew I (grabUrnInkNew σ I) (grabUrnArtNew σ I)
              (grabIlkArtNew σ I)).insert "dtab" (.int dtab) }
        evm3
        (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
          (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
            (.storage (ilksF (.var "i") "rate")))) =
        .ok (.bool true))
    (hDtabWord : dtabWord = grabDtab σ I)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hInkNeg :
      0 ≤ grabDinkInt I ∨
        (grabUrnInkNew σ I).toNat ≤ (vatSlotWord (grabUrnInkSlot I) σ I).toNat)
    (hInkPos :
      grabDinkInt I ≤ 0 ∨
        (vatSlotWord (grabUrnInkSlot I) σ I).toNat ≤ (grabUrnInkNew σ I).toNat)
    (hUrnArtNeg :
      0 ≤ grabDartInt I ∨
        (grabUrnArtNew σ I).toNat ≤
          (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)).toNat)
    (hUrnArtPos :
      grabDartInt I ≤ 0 ∨
        (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)).toNat ≤
          (grabUrnArtNew σ I).toNat)
    (hIlkArtNeg :
      0 ≤ grabDartInt I ∨
        (grabIlkArtNew σ I).toNat ≤
          (solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I)).toNat)
    (hIlkArtPos :
      grabDartInt I ≤ 0 ∨
        (solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I)).toNat ≤
          (grabIlkArtNew σ I).toNat)
    (hGemNeg :
      grabDinkInt I ≤ 0 ∨
        (grabGemNew σ I).toNat ≤
          (solcSlotWord (grabAfterIlkArt σ I) I (grabGemVSlot I)).toNat)
    (hGemPos :
      0 ≤ grabDinkInt I ∨
        (solcSlotWord (grabAfterIlkArt σ I) I (grabGemVSlot I)).toNat ≤
          (grabGemNew σ I).toNat)
    (hSinNeg :
      dtab ≤ 0 ∨
        (grabSinNew σ I).toNat ≤
          (solcSlotWord (grabAfterGem σ I) I (grabSinSlot I)).toNat)
    (hSinPos :
      0 ≤ dtab ∨
        (solcSlotWord (grabAfterGem σ I) I (grabSinSlot I)).toNat ≤
          (grabSinNew σ I).toNat)
    (hViceNeg :
      dtab ≤ 0 ∨
        (grabViceNew σ I).toNat ≤
          (solcSlotWord (grabAfterSin σ I) I ⟨8⟩).toNat)
    (hVicePos :
      0 ≤ dtab ∨
        (solcSlotWord (grabAfterSin σ I) I ⟨8⟩).toNat ≤
          (grabViceNew σ I).toNat) :
    let urnInkNew := grabUrnInkNew σ I
    let urnArtNew := grabUrnArtNew σ I
    let ilkArtNew := grabIlkArtNew σ I
    let gemNew := grabGemNew σ I
    let sinNew := grabSinNew σ I
    let viceNew := grabViceNew σ I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
      (grabUrnInkSourceSlot I) urnInkNew
    let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
      (grabUrnArtSourceSlot I) urnArtNew
    let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
      (grabIlkArtSourceSlot I) ilkArtNew
    let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
      (grabGemSourceSlot I) gemNew
    let evm5 := Solm.EVM.storageStore evm4 evm4.executionEnv.codeOwner
      (grabSinSourceSlot I) sinNew
    let evm6 := Solm.EVM.storageStore evm5 evm5.executionEnv.codeOwner grabViceSourceSlot viceNew
    let finalLocals :=
      grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew viceNew
    ExecTransitionBody config contract evm0 (grabStore I) grabTransition.body
      (.returned { contract := contract, locals := finalLocals } evm6 none) := by
  intro urnInkNew urnArtNew ilkArtNew gemNew sinNew viceNew evm0 evm1 evm2 evm3 evm4 evm5
    evm6 finalLocals
  exact execGrabSourceOk (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hwei hauth hsz196
    (vatSlotWord (grabUrnInkSlot I) σ I) (grabUrnInkNew σ I)
    (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)) (grabUrnArtNew σ I)
    (solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I)) (grabIlkArtNew σ I)
    (solcSlotWord (grabAfterIlkArt σ I) I (grabIlkRateSlot I))
    dtab dtabWord
    (solcSlotWord (grabAfterIlkArt σ I) I (grabGemVSlot I)) (grabGemNew σ I)
    (solcSlotWord (grabAfterGem σ I) I (grabSinSlot I)) (grabSinNew σ I)
    (solcSlotWord (grabAfterSin σ I) I ⟨8⟩) (grabViceNew σ I)
    (by simpa using
      (grabSourceLoad_urnInk (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
    (by simp [grabUrnInkNew, vatSlotWord])
    hInkNeg hInkPos
    (by simpa using
      (grabSourceLoad_urnArt_staged (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
    (by simp [grabUrnArtNew])
    hUrnArtNeg hUrnArtPos
    (by simpa using
      (grabSourceLoad_ilkArt_staged (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
    (by simp [grabIlkArtNew]) hIlkArtNeg hIlkArtPos
    (by simpa using
      (grabSourceLoad_ilkRate_staged (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
    hDtab hdtabLo hdtabHi hguardMax hguardMul
    (by simpa using
      (grabSourceLoad_gem_staged (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
    (by simp [grabGemNew]) hGemNeg hGemPos
    (by simpa using
      (grabSourceLoad_sin_staged (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
    hdtabMod (by simp [grabSinNew, hDtabWord]) hSinNeg hSinPos
    (by simpa using
      (grabSourceLoad_vice_staged (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
    (by simp [grabViceNew, hDtabWord]) hViceNeg hVicePos

theorem vatGrabSourceBodySuccessFromRuntimeGuards
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hwei : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz196 : 196 ≤ I.calldata.size)
    (dtab : Int) (dtabWord : UInt256)
    (hDtab :
      dtab =
        Int.ofNat (solcSlotWord (grabAfterIlkArt σ_solm I) I (grabIlkRateSlot I)).toNat *
          grabDartInt I)
    (hDtabWord : dtabWord = grabDtab σ_solm I)
    (hdtabLo : -((2 : Int) ^ 255) ≤ dtab)
    (hdtabHi : dtab < (2 : Int) ^ 255)
    (hdtabMod : dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat)
    (hguardMax :
      evalExpr? config
        { contract := contract,
          locals :=
            (grabStoreIlkArtNew I (grabUrnInkNew σ_solm I) (grabUrnArtNew σ_solm I)
              (grabIlkArtNew σ_solm I)).insert "dtab" (.int dtab) }
        (grabSourceEvm3 cA gh bl σ_solm σ₀ A I g
          (grabUrnInkNew σ_solm I) (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I))
        (.binary .le (.storage (ilksF (.var "i") "rate")) (.intLit maxInt256)) =
        .ok (.bool true))
    (hguardMul :
      evalExpr? config
        { contract := contract,
          locals :=
            (grabStoreIlkArtNew I (grabUrnInkNew σ_solm I) (grabUrnArtNew σ_solm I)
              (grabIlkArtNew σ_solm I)).insert "dtab" (.int dtab) }
        (grabSourceEvm3 cA gh bl σ_solm σ₀ A I g
          (grabUrnInkNew σ_solm I) (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I))
        (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
          (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
            (.storage (ilksF (.var "i") "rate")))) =
        .ok (.bool true))
    (hInkNeg : grabInkNegOk σ_evm I) (hInkPos : grabInkPosOk σ_evm I)
    (hUrnArtNeg : grabUrnArtNegOk σ_evm I)
    (hUrnArtPos : grabUrnArtPosOk σ_evm I)
    (hIlkArtNeg : grabIlkArtNegOk σ_evm I)
    (hIlkArtPos : grabIlkArtPosOk σ_evm I)
    (hDtabMax : grabDtabMaxOk σ_evm I) (hDtabMul : grabDtabMulOk σ_evm I)
    (hGemPos : grabGemPosOk σ_evm I) (hGemNeg : grabGemNegOk σ_evm I)
    (hSinPos : grabSinPosOk σ_evm I) (hSinNeg : grabSinNegOk σ_evm I)
    (hVicePos : grabVicePosOk σ_evm I) (hViceNeg : grabViceNegOk σ_evm I) :
    let urnInkNew := grabUrnInkNew σ_solm I
    let urnArtNew := grabUrnArtNew σ_solm I
    let ilkArtNew := grabIlkArtNew σ_solm I
    let gemNew := grabGemNew σ_solm I
    let sinNew := grabSinNew σ_solm I
    let viceNew := grabViceNew σ_solm I
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
      (grabUrnInkSourceSlot I) urnInkNew
    let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
      (grabUrnArtSourceSlot I) urnArtNew
    let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
      (grabIlkArtSourceSlot I) ilkArtNew
    let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
      (grabGemSourceSlot I) gemNew
    let evm5 := Solm.EVM.storageStore evm4 evm4.executionEnv.codeOwner
      (grabSinSourceSlot I) sinNew
    let evm6 := Solm.EVM.storageStore evm5 evm5.executionEnv.codeOwner grabViceSourceSlot viceNew
    let finalLocals :=
      grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew viceNew
    ExecTransitionBody config contract evm0 (grabStore I) grabTransition.body
      (.returned { contract := contract, locals := finalLocals } evm6 none) := by
  rcases accountMapEquiv_grabGuards hAccounts hInkNeg hInkPos hUrnArtNeg
      hUrnArtPos hIlkArtNeg hIlkArtPos hDtabMax hDtabMul hGemPos hGemNeg hSinPos
      hSinNeg hVicePos hViceNeg with
    ⟨hInkNegS, hInkPosS, hUrnArtNegS, hUrnArtPosS, hIlkArtNegS,
      hIlkArtPosS, _, _, hGemPosS, hGemNegS, hSinPosS, hSinNegS, hVicePosS,
      hViceNegS⟩
  exact vatGrabSourceBodySuccessFromFinalValues
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hwei hauth hsz196 dtab dtabWord
    hDtab hdtabLo hdtabHi hguardMax hguardMul hDtabWord hdtabMod
    (grabDinkAddGuardNegCond hInkNegS)
    (grabDinkAddGuardPosCond hInkPosS)
    (grabDartAddGuardNegCond hUrnArtNegS)
    (grabDartAddGuardPosCond hUrnArtPosS)
    (grabDartAddGuardNegCond hIlkArtNegS)
    (grabDartAddGuardPosCond hIlkArtPosS)
    (grabDinkSubGuardNegCond hGemPosS)
    (grabDinkSubGuardPosCond hGemNegS)
    (grabDtabSubGuardNegCond hdtabLo hdtabHi hdtabMod
      (by simpa [grabSinPosOk, hDtabWord] using hSinPosS))
    (grabDtabSubGuardPosCond hdtabLo hdtabHi hdtabMod
      (by simpa [grabSinNegOk, hDtabWord] using hSinNegS))
    (grabDtabSubGuardNegCond hdtabLo hdtabHi hdtabMod
      (by simpa [grabVicePosOk, hDtabWord] using hVicePosS))
    (grabDtabSubGuardPosCond hdtabLo hdtabHi hdtabMod
      (by simpa [grabViceNegOk, hDtabWord] using hViceNegS))

theorem vatGrabSourceBodyUrnInkRevertGuardNeg
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwei : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hsz196 : 196 ≤ I.calldata.size)
    (hguardNeg :
      grabDinkInt I < 0 ∧
        (vatSlotWord (grabUrnInkSlot I) σ I).toNat < (grabUrnInkNew σ I).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (grabStore I) grabTransition.body .reverted := by
  intro evm0
  have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := grabStore I)
    (grabStore_get_wards I) hauth
  have hprefix :
      ExecBlock config { contract := contract, locals := grabStore I } evm0
        (nonpayable ++ auth) (.ok { contract := contract, locals := grabStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := grabStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]
      (.ok { contract := contract, locals := grabStore I } evm0)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwei)
    exact ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ExecBlock.nil
  have hInkRevert :
      ExecBlock config { contract := contract, locals := grabStore I } evm0
        (checkedAddSignedInto "urnInkNew"
          (.storage (urnsF (.var "i") (.var "u") "ink")) (.var "dink"))
        .reverted := by
    exact execGrabUrnInkCheckedRevertGuardNeg (evm := evm0) (I := I)
      (grabStore I) (vatSlotWord (grabUrnInkSlot I) σ I) (grabUrnInkNew σ I)
      hsz196 (grabStore_get_i I) (grabStore_get_u I) (grabStore_get_dink I)
      (grabStore_urns I)
      (by
        simpa [evm0] using
          (grabSourceLoad_urnInk (cA := cA) (gh := gh) (bl := bl)
            (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
      (by simp [grabUrnInkNew, vatSlotWord]) hguardNeg
  have h01 :=.execBlock_append hprefix hInkRevert
  have hblock :=.execBlock_append_term
    (s2 :=
      [ .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew") ] ++
      checkedAddSignedInto "urnArtNew" (.storage (urnsF (.var "i") (.var "u") "art"))
        (.var "dart") ++
      [ .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew") ] ++
      checkedAddSignedInto "ilkArtNew" (.storage (ilksF (.var "i") "Art"))
        (.var "dart") ++
      [ .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew") ] ++
      checkedMulSignedInto "dtab" (.storage (ilksF (.var "i") "rate")) (.var "dart") ++
      checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
      checkedSubSignedInto "sinNew" (.storage (sinRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (sinRef (.var "w")) (.var "sinNew") ] ++
      checkedSubSignedInto "viceNew" (.storage viceRef) (.var "dtab") ++
      [ .assign .storage viceRef (.var "viceNew") ])
    h01 (by intro f e h; cases h)
  simpa [ExecTransitionBody, grabTransition, nonpayable, auth, evm0, List.append_assoc]
    using ExecFuncBody.execBlockRevert hblock

theorem vatGrabSourceBodyUrnInkRevertGuardPos
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwei : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hsz196 : 196 ≤ I.calldata.size)
    (hguardNeg :
      0 ≤ grabDinkInt I ∨
        (grabUrnInkNew σ I).toNat ≤ (vatSlotWord (grabUrnInkSlot I) σ I).toNat)
    (hguardPos :
      0 < grabDinkInt I ∧
        (grabUrnInkNew σ I).toNat < (vatSlotWord (grabUrnInkSlot I) σ I).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (grabStore I) grabTransition.body .reverted := by
  intro evm0
  have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := grabStore I)
    (grabStore_get_wards I) hauth
  have hprefix :
      ExecBlock config { contract := contract, locals := grabStore I } evm0
        (nonpayable ++ auth) (.ok { contract := contract, locals := grabStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := grabStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]
      (.ok { contract := contract, locals := grabStore I } evm0)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwei)
    exact ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ExecBlock.nil
  have hInkRevert :
      ExecBlock config { contract := contract, locals := grabStore I } evm0
        (checkedAddSignedInto "urnInkNew"
          (.storage (urnsF (.var "i") (.var "u") "ink")) (.var "dink"))
        .reverted := by
    exact execGrabUrnInkCheckedRevertGuardPos (evm := evm0) (I := I)
      (grabStore I) (vatSlotWord (grabUrnInkSlot I) σ I) (grabUrnInkNew σ I)
      hsz196 (grabStore_get_i I) (grabStore_get_u I) (grabStore_get_dink I)
      (grabStore_urns I)
      (by
        simpa [evm0] using
          (grabSourceLoad_urnInk (cA := cA) (gh := gh) (bl := bl)
            (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
      (by simp [grabUrnInkNew, vatSlotWord]) hguardNeg hguardPos
  have h01 :=.execBlock_append hprefix hInkRevert
  have hblock :=.execBlock_append_term
    (s2 :=
      [ .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew") ] ++
      checkedAddSignedInto "urnArtNew" (.storage (urnsF (.var "i") (.var "u") "art"))
        (.var "dart") ++
      [ .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew") ] ++
      checkedAddSignedInto "ilkArtNew" (.storage (ilksF (.var "i") "Art"))
        (.var "dart") ++
      [ .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew") ] ++
      checkedMulSignedInto "dtab" (.storage (ilksF (.var "i") "rate")) (.var "dart") ++
      checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
      checkedSubSignedInto "sinNew" (.storage (sinRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (sinRef (.var "w")) (.var "sinNew") ] ++
      checkedSubSignedInto "viceNew" (.storage viceRef) (.var "dtab") ++
      [ .assign .storage viceRef (.var "viceNew") ])
    h01 (by intro f e h; cases h)
  simpa [ExecTransitionBody, grabTransition, nonpayable, auth, evm0, List.append_assoc]
    using ExecFuncBody.execBlockRevert hblock

theorem vatGrabSourceBodyUrnArtRevertFromBlock
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwei : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hsz196 : 196 ≤ I.calldata.size)
    (hinkNeg :
      0 ≤ grabDinkInt I ∨
        (grabUrnInkNew σ I).toNat ≤
          (vatSlotWord (grabUrnInkSlot I) σ I).toNat)
    (hinkPos :
      grabDinkInt I ≤ 0 ∨
        (vatSlotWord (grabUrnInkSlot I) σ I).toNat ≤
          (grabUrnInkNew σ I).toNat)
    (hArtRevert :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
        (grabUrnInkSourceSlot I) (grabUrnInkNew σ I)
      ExecBlock config
        { contract := contract, locals := grabStoreUrnInkNew I (grabUrnInkNew σ I) } evm1
        (checkedAddSignedInto "urnArtNew"
          (.storage (urnsF (.var "i") (.var "u") "art")) (.var "dart"))
        .reverted) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (grabStore I) grabTransition.body .reverted := by
  intro evm0
  let urnInkNew := grabUrnInkNew σ I
  let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
    (grabUrnInkSourceSlot I) urnInkNew
  let localsInk := grabStoreUrnInkNew I urnInkNew
  have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := grabStore I)
    (grabStore_get_wards I) hauth
  have hprefix :
      ExecBlock config { contract := contract, locals := grabStore I } evm0
        (nonpayable ++ auth) (.ok { contract := contract, locals := grabStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := grabStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]
      (.ok { contract := contract, locals := grabStore I } evm0)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwei)
    exact ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ExecBlock.nil
  have hInkBlock :
      ExecBlock config { contract := contract, locals := grabStore I } evm0
        (checkedAddSignedInto "urnInkNew"
          (.storage (urnsF (.var "i") (.var "u") "ink")) (.var "dink") ++
          [ .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew") ])
        (.ok { contract := contract, locals := localsInk } evm1) := by
    exact execGrabUrnInkUpdateOk (evm := evm0) (I := I) (locals := grabStore I)
      (vatSlotWord (grabUrnInkSlot I) σ I) urnInkNew hsz196
      (grabStore_get_i I) (grabStore_get_u I) (grabStore_get_dink I)
      (grabStore_urns I)
      (by
        simpa [evm0] using
          (grabSourceLoad_urnInk (cA := cA) (gh := gh) (bl := bl)
            (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
      (by simp [urnInkNew, grabUrnInkNew, vatSlotWord])
      (by simpa [urnInkNew, vatSlotWord] using hinkNeg)
      (by simpa [urnInkNew, vatSlotWord] using hinkPos)
  have h01 :=.execBlock_append hprefix hInkBlock
  have hArt : ExecBlock config { contract := contract, locals := localsInk } evm1
      (checkedAddSignedInto "urnArtNew"
        (.storage (urnsF (.var "i") (.var "u") "art")) (.var "dart"))
      .reverted := by
    simpa [evm0, evm1, localsInk, urnInkNew] using hArtRevert
  have h02 :=.execBlock_append h01 hArt
  have hblock :=.execBlock_append_term
    (s2 :=
      [ .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew") ] ++
      checkedAddSignedInto "ilkArtNew" (.storage (ilksF (.var "i") "Art"))
        (.var "dart") ++
      [ .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew") ] ++
      checkedMulSignedInto "dtab" (.storage (ilksF (.var "i") "rate")) (.var "dart") ++
      checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
      checkedSubSignedInto "sinNew" (.storage (sinRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (sinRef (.var "w")) (.var "sinNew") ] ++
      checkedSubSignedInto "viceNew" (.storage viceRef) (.var "dtab") ++
      [ .assign .storage viceRef (.var "viceNew") ])
    h02 (by intro f e h; cases h)
  simpa [ExecTransitionBody, grabTransition, nonpayable, auth, evm0, evm1, localsInk,
    urnInkNew, List.append_assoc] using ExecFuncBody.execBlockRevert hblock

theorem vatGrabSourceBodyUrnArtRevertGuardNeg
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwei : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hsz196 : 196 ≤ I.calldata.size)
    (hinkNeg :
      0 ≤ grabDinkInt I ∨
        (grabUrnInkNew σ I).toNat ≤
          (vatSlotWord (grabUrnInkSlot I) σ I).toNat)
    (hinkPos :
      grabDinkInt I ≤ 0 ∨
        (vatSlotWord (grabUrnInkSlot I) σ I).toNat ≤
          (grabUrnInkNew σ I).toNat)
    (hguardNeg :
      grabDartInt I < 0 ∧
        (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)).toNat <
          (grabUrnArtNew σ I).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (grabStore I) grabTransition.body .reverted := by
  refine vatGrabSourceBodyUrnArtRevertFromBlock
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hwei hauth hsz196 hinkNeg hinkPos ?_
  intro evm0 evm1
  exact execGrabUrnArtCheckedRevertGuardNeg (evm := evm1) (I := I)
    (grabStoreUrnInkNew I (grabUrnInkNew σ I))
    (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)) (grabUrnArtNew σ I)
    hsz196
    (by
      change ((grabStore I).insert "urnInkNew"
        (.int (Int.ofNat (grabUrnInkNew σ I).toNat))).get? "i" = some (grabIValue I)
      rw [store_get_ne _ _ (by native_decide)]
      exact grabStore_get_i I)
    (by
      change ((grabStore I).insert "urnInkNew"
        (.int (Int.ofNat (grabUrnInkNew σ I).toNat))).get? "u" = some (grabUValue I)
      rw [store_get_ne _ _ (by native_decide)]
      exact grabStore_get_u I)
    (by
      change ((grabStore I).insert "urnInkNew"
        (.int (Int.ofNat (grabUrnInkNew σ I).toNat))).get? "dart" =
        some (grabDartValue I)
      rw [store_get_ne _ _ (by native_decide)]
      exact grabStore_get_dart I)
    (by
      change ((grabStore I).insert "urnInkNew"
        (.int (Int.ofNat (grabUrnInkNew σ I).toNat))).get? "urns" = none
      rw [store_get_ne _ _ (by native_decide)]
      exact grabStore_urns I)
    (by simpa [evm0, evm1] using
      (grabSourceLoad_urnArt_staged (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
    (by simp [grabUrnArtNew]) hguardNeg

theorem vatGrabSourceBodyUrnArtRevertGuardPos
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwei : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hsz196 : 196 ≤ I.calldata.size)
    (hinkNeg :
      0 ≤ grabDinkInt I ∨
        (grabUrnInkNew σ I).toNat ≤
          (vatSlotWord (grabUrnInkSlot I) σ I).toNat)
    (hinkPos :
      grabDinkInt I ≤ 0 ∨
        (vatSlotWord (grabUrnInkSlot I) σ I).toNat ≤
          (grabUrnInkNew σ I).toNat)
    (hguardNeg :
      0 ≤ grabDartInt I ∨
        (grabUrnArtNew σ I).toNat ≤
          (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)).toNat)
    (hguardPos :
      0 < grabDartInt I ∧
        (grabUrnArtNew σ I).toNat <
          (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (grabStore I) grabTransition.body .reverted := by
  refine vatGrabSourceBodyUrnArtRevertFromBlock
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hwei hauth hsz196 hinkNeg hinkPos ?_
  intro evm0 evm1
  exact execGrabUrnArtCheckedRevertGuardPos (evm := evm1) (I := I)
    (grabStoreUrnInkNew I (grabUrnInkNew σ I))
    (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)) (grabUrnArtNew σ I)
    hsz196
    (by
      change ((grabStore I).insert "urnInkNew"
        (.int (Int.ofNat (grabUrnInkNew σ I).toNat))).get? "i" = some (grabIValue I)
      rw [store_get_ne _ _ (by native_decide)]
      exact grabStore_get_i I)
    (by
      change ((grabStore I).insert "urnInkNew"
        (.int (Int.ofNat (grabUrnInkNew σ I).toNat))).get? "u" = some (grabUValue I)
      rw [store_get_ne _ _ (by native_decide)]
      exact grabStore_get_u I)
    (by
      change ((grabStore I).insert "urnInkNew"
        (.int (Int.ofNat (grabUrnInkNew σ I).toNat))).get? "dart" =
        some (grabDartValue I)
      rw [store_get_ne _ _ (by native_decide)]
      exact grabStore_get_dart I)
    (by
      change ((grabStore I).insert "urnInkNew"
        (.int (Int.ofNat (grabUrnInkNew σ I).toNat))).get? "urns" = none
      rw [store_get_ne _ _ (by native_decide)]
      exact grabStore_urns I)
    (by simpa [evm0, evm1] using
      (grabSourceLoad_urnArt_staged (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
    (by simp [grabUrnArtNew]) hguardNeg hguardPos

theorem vatGrabSourceBodyIlkArtRevertFromBlock
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwei : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hsz196 : 196 ≤ I.calldata.size)
    (hinkNeg :
      0 ≤ grabDinkInt I ∨
        (grabUrnInkNew σ I).toNat ≤
          (vatSlotWord (grabUrnInkSlot I) σ I).toNat)
    (hinkPos :
      grabDinkInt I ≤ 0 ∨
        (vatSlotWord (grabUrnInkSlot I) σ I).toNat ≤
          (grabUrnInkNew σ I).toNat)
    (hartNeg :
      0 ≤ grabDartInt I ∨
        (grabUrnArtNew σ I).toNat ≤
          (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)).toNat)
    (hartPos :
      grabDartInt I ≤ 0 ∨
        (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)).toNat ≤
          (grabUrnArtNew σ I).toNat)
    (hIlkRevert :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
        (grabUrnInkSourceSlot I) (grabUrnInkNew σ I)
      let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
        (grabUrnArtSourceSlot I) (grabUrnArtNew σ I)
      ExecBlock config
        { contract := contract,
          locals := grabStoreUrnArtNew I (grabUrnInkNew σ I) (grabUrnArtNew σ I) } evm2
        (checkedAddSignedInto "ilkArtNew" (.storage (ilksF (.var "i") "Art"))
          (.var "dart"))
        .reverted) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (grabStore I) grabTransition.body .reverted := by
  intro evm0
  let urnInkNew := grabUrnInkNew σ I
  let urnArtNew := grabUrnArtNew σ I
  let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
    (grabUrnInkSourceSlot I) urnInkNew
  let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
    (grabUrnArtSourceSlot I) urnArtNew
  let localsInk := grabStoreUrnInkNew I urnInkNew
  let localsArt := grabStoreUrnArtNew I urnInkNew urnArtNew
  have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := grabStore I)
    (grabStore_get_wards I) hauth
  have hprefix :
      ExecBlock config { contract := contract, locals := grabStore I } evm0
        (nonpayable ++ auth) (.ok { contract := contract, locals := grabStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := grabStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]
      (.ok { contract := contract, locals := grabStore I } evm0)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwei)
    exact ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ExecBlock.nil
  have hInkBlock :
      ExecBlock config { contract := contract, locals := grabStore I } evm0
        (checkedAddSignedInto "urnInkNew"
          (.storage (urnsF (.var "i") (.var "u") "ink")) (.var "dink") ++
          [ .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew") ])
        (.ok { contract := contract, locals := localsInk } evm1) := by
    exact execGrabUrnInkUpdateOk (evm := evm0) (I := I) (locals := grabStore I)
      (vatSlotWord (grabUrnInkSlot I) σ I) urnInkNew hsz196
      (grabStore_get_i I) (grabStore_get_u I) (grabStore_get_dink I)
      (grabStore_urns I)
      (by
        simpa [evm0] using
          (grabSourceLoad_urnInk (cA := cA) (gh := gh) (bl := bl)
            (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
      (by simp [urnInkNew, grabUrnInkNew, vatSlotWord])
      (by simpa [urnInkNew, vatSlotWord] using hinkNeg)
      (by simpa [urnInkNew, vatSlotWord] using hinkPos)
  have hArt_i : localsInk.get? "i" = some (grabIValue I) := by
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "i" =
      some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact grabStore_get_i I
  have hArt_u : localsInk.get? "u" = some (grabUValue I) := by
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "u" =
      some (grabUValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact grabStore_get_u I
  have hArt_dart : localsInk.get? "dart" = some (grabDartValue I) := by
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get?
      "dart" = some (grabDartValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact grabStore_get_dart I
  have hArt_urns : localsInk.get? "urns" = none := by
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get?
      "urns" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact grabStore_urns I
  have hArtBlock :
      ExecBlock config { contract := contract, locals := localsInk } evm1
        (checkedAddSignedInto "urnArtNew"
          (.storage (urnsF (.var "i") (.var "u") "art")) (.var "dart") ++
          [ .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew") ])
        (.ok { contract := contract, locals := localsArt } evm2) := by
    exact execGrabUrnArtUpdateOk (evm := evm1) (I := I) (locals := localsInk)
      (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)) urnArtNew hsz196
      hArt_i hArt_u hArt_dart hArt_urns
      (by simpa [evm0, evm1] using
        (grabSourceLoad_urnArt_staged (cA := cA) (gh := gh) (bl := bl)
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
      (by simp [urnArtNew, grabUrnArtNew])
      (by simpa [urnArtNew] using hartNeg)
      (by simpa [urnArtNew] using hartPos)
  have h01 :=.execBlock_append hprefix hInkBlock
  have h02 :=.execBlock_append h01 hArtBlock
  have hIlk : ExecBlock config { contract := contract, locals := localsArt } evm2
      (checkedAddSignedInto "ilkArtNew" (.storage (ilksF (.var "i") "Art"))
        (.var "dart"))
      .reverted := by
    simpa [evm0, evm1, evm2, localsArt, urnInkNew, urnArtNew] using hIlkRevert
  have h03 :=.execBlock_append h02 hIlk
  have hblock :=.execBlock_append_term
    (s2 :=
      [ .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew") ] ++
      checkedMulSignedInto "dtab" (.storage (ilksF (.var "i") "rate")) (.var "dart") ++
      checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
      checkedSubSignedInto "sinNew" (.storage (sinRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (sinRef (.var "w")) (.var "sinNew") ] ++
      checkedSubSignedInto "viceNew" (.storage viceRef) (.var "dtab") ++
      [ .assign .storage viceRef (.var "viceNew") ])
    h03 (by intro f e h; cases h)
  simpa [ExecTransitionBody, grabTransition, nonpayable, auth, evm0, evm1, evm2,
    localsInk, localsArt, urnInkNew, urnArtNew, List.append_assoc]
    using ExecFuncBody.execBlockRevert hblock

theorem vatGrabSourceBodyIlkArtRevertGuardNeg
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwei : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hsz196 : 196 ≤ I.calldata.size)
    (hinkNeg :
      0 ≤ grabDinkInt I ∨
        (grabUrnInkNew σ I).toNat ≤
          (vatSlotWord (grabUrnInkSlot I) σ I).toNat)
    (hinkPos :
      grabDinkInt I ≤ 0 ∨
        (vatSlotWord (grabUrnInkSlot I) σ I).toNat ≤
          (grabUrnInkNew σ I).toNat)
    (hartNeg :
      0 ≤ grabDartInt I ∨
        (grabUrnArtNew σ I).toNat ≤
          (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)).toNat)
    (hartPos :
      grabDartInt I ≤ 0 ∨
        (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)).toNat ≤
          (grabUrnArtNew σ I).toNat)
    (hguardNeg :
      grabDartInt I < 0 ∧
        (solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I)).toNat <
          (grabIlkArtNew σ I).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (grabStore I) grabTransition.body .reverted := by
  refine vatGrabSourceBodyIlkArtRevertFromBlock
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hwei hauth hsz196 hinkNeg hinkPos hartNeg hartPos ?_
  intro evm0 evm1 evm2
  exact execGrabIlkArtCheckedRevertGuardNeg (evm := evm2) (I := I)
    (grabStoreUrnArtNew I (grabUrnInkNew σ I) (grabUrnArtNew σ I))
    (solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I)) (grabIlkArtNew σ I)
    hsz196
    (by
      change ((grabStoreUrnInkNew I (grabUrnInkNew σ I)).insert "urnArtNew"
        (.int (Int.ofNat (grabUrnArtNew σ I).toNat))).get? "i" = some (grabIValue I)
      rw [store_get_ne _ _ (by native_decide)]
      change ((grabStore I).insert "urnInkNew"
        (.int (Int.ofNat (grabUrnInkNew σ I).toNat))).get? "i" = some (grabIValue I)
      rw [store_get_ne _ _ (by native_decide)]
      exact grabStore_get_i I)
    (by
      change ((grabStoreUrnInkNew I (grabUrnInkNew σ I)).insert "urnArtNew"
        (.int (Int.ofNat (grabUrnArtNew σ I).toNat))).get? "dart" =
        some (grabDartValue I)
      rw [store_get_ne _ _ (by native_decide)]
      change ((grabStore I).insert "urnInkNew"
        (.int (Int.ofNat (grabUrnInkNew σ I).toNat))).get? "dart" =
        some (grabDartValue I)
      rw [store_get_ne _ _ (by native_decide)]
      exact grabStore_get_dart I)
    (by
      change ((grabStoreUrnInkNew I (grabUrnInkNew σ I)).insert "urnArtNew"
        (.int (Int.ofNat (grabUrnArtNew σ I).toNat))).get? "ilks" = none
      rw [store_get_ne _ _ (by native_decide)]
      change ((grabStore I).insert "urnInkNew"
        (.int (Int.ofNat (grabUrnInkNew σ I).toNat))).get? "ilks" = none
      rw [store_get_ne _ _ (by native_decide)]
      simp [grabStore])
    (by simpa [evm0, evm1, evm2] using
      (grabSourceLoad_ilkArt_staged (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
    (by simp [grabIlkArtNew]) hguardNeg

theorem vatGrabSourceBodyIlkArtRevertGuardPos
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwei : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hsz196 : 196 ≤ I.calldata.size)
    (hinkNeg :
      0 ≤ grabDinkInt I ∨
        (grabUrnInkNew σ I).toNat ≤
          (vatSlotWord (grabUrnInkSlot I) σ I).toNat)
    (hinkPos :
      grabDinkInt I ≤ 0 ∨
        (vatSlotWord (grabUrnInkSlot I) σ I).toNat ≤
          (grabUrnInkNew σ I).toNat)
    (hartNeg :
      0 ≤ grabDartInt I ∨
        (grabUrnArtNew σ I).toNat ≤
          (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)).toNat)
    (hartPos :
      grabDartInt I ≤ 0 ∨
        (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)).toNat ≤
          (grabUrnArtNew σ I).toNat)
    (hguardNeg :
      0 ≤ grabDartInt I ∨
        (grabIlkArtNew σ I).toNat ≤
          (solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I)).toNat)
    (hguardPos :
      0 < grabDartInt I ∧
        (grabIlkArtNew σ I).toNat <
          (solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I)).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (grabStore I) grabTransition.body .reverted := by
  refine vatGrabSourceBodyIlkArtRevertFromBlock
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hwei hauth hsz196 hinkNeg hinkPos hartNeg hartPos ?_
  intro evm0 evm1 evm2
  exact execGrabIlkArtCheckedRevertGuardPos (evm := evm2) (I := I)
    (grabStoreUrnArtNew I (grabUrnInkNew σ I) (grabUrnArtNew σ I))
    (solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I)) (grabIlkArtNew σ I)
    hsz196
    (by
      change ((grabStoreUrnInkNew I (grabUrnInkNew σ I)).insert "urnArtNew"
        (.int (Int.ofNat (grabUrnArtNew σ I).toNat))).get? "i" = some (grabIValue I)
      rw [store_get_ne _ _ (by native_decide)]
      change ((grabStore I).insert "urnInkNew"
        (.int (Int.ofNat (grabUrnInkNew σ I).toNat))).get? "i" = some (grabIValue I)
      rw [store_get_ne _ _ (by native_decide)]
      exact grabStore_get_i I)
    (by
      change ((grabStoreUrnInkNew I (grabUrnInkNew σ I)).insert "urnArtNew"
        (.int (Int.ofNat (grabUrnArtNew σ I).toNat))).get? "dart" =
        some (grabDartValue I)
      rw [store_get_ne _ _ (by native_decide)]
      change ((grabStore I).insert "urnInkNew"
        (.int (Int.ofNat (grabUrnInkNew σ I).toNat))).get? "dart" =
        some (grabDartValue I)
      rw [store_get_ne _ _ (by native_decide)]
      exact grabStore_get_dart I)
    (by
      change ((grabStoreUrnInkNew I (grabUrnInkNew σ I)).insert "urnArtNew"
        (.int (Int.ofNat (grabUrnArtNew σ I).toNat))).get? "ilks" = none
      rw [store_get_ne _ _ (by native_decide)]
      change ((grabStore I).insert "urnInkNew"
        (.int (Int.ofNat (grabUrnInkNew σ I).toNat))).get? "ilks" = none
      rw [store_get_ne _ _ (by native_decide)]
      simp [grabStore])
    (by simpa [evm0, evm1, evm2] using
      (grabSourceLoad_ilkArt_staged (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
    (by simp [grabIlkArtNew]) hguardNeg hguardPos

theorem vatGrabSourceBodyDtabRevertFromBlock
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwei : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hsz196 : 196 ≤ I.calldata.size)
    (hinkNeg :
      0 ≤ grabDinkInt I ∨
        (grabUrnInkNew σ I).toNat ≤
          (vatSlotWord (grabUrnInkSlot I) σ I).toNat)
    (hinkPos :
      grabDinkInt I ≤ 0 ∨
        (vatSlotWord (grabUrnInkSlot I) σ I).toNat ≤
          (grabUrnInkNew σ I).toNat)
    (hartNeg :
      0 ≤ grabDartInt I ∨
        (grabUrnArtNew σ I).toNat ≤
          (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)).toNat)
    (hartPos :
      grabDartInt I ≤ 0 ∨
        (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)).toNat ≤
          (grabUrnArtNew σ I).toNat)
    (hilkNeg :
      0 ≤ grabDartInt I ∨
        (grabIlkArtNew σ I).toNat ≤
          (solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I)).toNat)
    (hilkPos :
      grabDartInt I ≤ 0 ∨
        (solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I)).toNat ≤
          (grabIlkArtNew σ I).toNat)
    (hDtabRevert :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
        (grabUrnInkSourceSlot I) (grabUrnInkNew σ I)
      let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
        (grabUrnArtSourceSlot I) (grabUrnArtNew σ I)
      let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
        (grabIlkArtSourceSlot I) (grabIlkArtNew σ I)
      ExecBlock config
        { contract := contract,
          locals := grabStoreIlkArtNew I (grabUrnInkNew σ I) (grabUrnArtNew σ I)
            (grabIlkArtNew σ I) } evm3
        (checkedMulSignedInto "dtab" (.storage (ilksF (.var "i") "rate")) (.var "dart"))
        .reverted) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (grabStore I) grabTransition.body .reverted := by
  intro evm0
  let urnInkNew := grabUrnInkNew σ I
  let urnArtNew := grabUrnArtNew σ I
  let ilkArtNew := grabIlkArtNew σ I
  let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
    (grabUrnInkSourceSlot I) urnInkNew
  let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
    (grabUrnArtSourceSlot I) urnArtNew
  let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
    (grabIlkArtSourceSlot I) ilkArtNew
  let localsInk := grabStoreUrnInkNew I urnInkNew
  let localsArt := grabStoreUrnArtNew I urnInkNew urnArtNew
  let localsIlk := grabStoreIlkArtNew I urnInkNew urnArtNew ilkArtNew
  have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := grabStore I)
    (grabStore_get_wards I) hauth
  have hprefix :
      ExecBlock config { contract := contract, locals := grabStore I } evm0
        (nonpayable ++ auth) (.ok { contract := contract, locals := grabStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := grabStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]
      (.ok { contract := contract, locals := grabStore I } evm0)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwei)
    exact ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ExecBlock.nil
  have hInkBlock :
      ExecBlock config { contract := contract, locals := grabStore I } evm0
        (checkedAddSignedInto "urnInkNew"
          (.storage (urnsF (.var "i") (.var "u") "ink")) (.var "dink") ++
          [ .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew") ])
        (.ok { contract := contract, locals := localsInk } evm1) := by
    exact execGrabUrnInkUpdateOk (evm := evm0) (I := I) (locals := grabStore I)
      (vatSlotWord (grabUrnInkSlot I) σ I) urnInkNew hsz196
      (grabStore_get_i I) (grabStore_get_u I) (grabStore_get_dink I)
      (grabStore_urns I)
      (by
        simpa [evm0] using
          (grabSourceLoad_urnInk (cA := cA) (gh := gh) (bl := bl)
            (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
      (by simp [urnInkNew, grabUrnInkNew, vatSlotWord])
      (by simpa [urnInkNew, vatSlotWord] using hinkNeg)
      (by simpa [urnInkNew, vatSlotWord] using hinkPos)
  have hArt_i : localsInk.get? "i" = some (grabIValue I) := by
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "i" =
      some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact grabStore_get_i I
  have hArt_u : localsInk.get? "u" = some (grabUValue I) := by
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "u" =
      some (grabUValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact grabStore_get_u I
  have hArt_dart : localsInk.get? "dart" = some (grabDartValue I) := by
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get?
      "dart" = some (grabDartValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact grabStore_get_dart I
  have hArt_urns : localsInk.get? "urns" = none := by
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get?
      "urns" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact grabStore_urns I
  have hArtBlock :
      ExecBlock config { contract := contract, locals := localsInk } evm1
        (checkedAddSignedInto "urnArtNew"
          (.storage (urnsF (.var "i") (.var "u") "art")) (.var "dart") ++
          [ .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew") ])
        (.ok { contract := contract, locals := localsArt } evm2) := by
    exact execGrabUrnArtUpdateOk (evm := evm1) (I := I) (locals := localsInk)
      (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)) urnArtNew hsz196
      hArt_i hArt_u hArt_dart hArt_urns
      (by simpa [evm0, evm1] using
        (grabSourceLoad_urnArt_staged (cA := cA) (gh := gh) (bl := bl)
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
      (by simp [urnArtNew, grabUrnArtNew])
      (by simpa [urnArtNew] using hartNeg)
      (by simpa [urnArtNew] using hartPos)
  have hIlk_i : localsArt.get? "i" = some (grabIValue I) := by
    change ((grabStoreUrnInkNew I urnInkNew).insert "urnArtNew"
      (.int (Int.ofNat urnArtNew.toNat))).get? "i" = some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hArt_i
  have hIlk_dart : localsArt.get? "dart" = some (grabDartValue I) := by
    change ((grabStoreUrnInkNew I urnInkNew).insert "urnArtNew"
      (.int (Int.ofNat urnArtNew.toNat))).get? "dart" = some (grabDartValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hArt_dart
  have hIlk_ilks : localsArt.get? "ilks" = none := by
    change ((grabStoreUrnInkNew I urnInkNew).insert "urnArtNew"
      (.int (Int.ofNat urnArtNew.toNat))).get? "ilks" = none
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get?
      "ilks" = none
    rw [store_get_ne _ _ (by native_decide)]
    simp [grabStore]
  have hIlkBlock :
      ExecBlock config { contract := contract, locals := localsArt } evm2
        (checkedAddSignedInto "ilkArtNew" (.storage (ilksF (.var "i") "Art"))
          (.var "dart") ++
          [ .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew") ])
        (.ok { contract := contract, locals := localsIlk } evm3) := by
    exact execGrabIlkArtUpdateOk (evm := evm2) (I := I) (locals := localsArt)
      (solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I)) ilkArtNew hsz196
      hIlk_i hIlk_dart hIlk_ilks
      (by simpa [evm0, evm1, evm2] using
        (grabSourceLoad_ilkArt_staged (cA := cA) (gh := gh) (bl := bl)
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
      (by simp [ilkArtNew, grabIlkArtNew])
      (by simpa [ilkArtNew] using hilkNeg)
      (by simpa [ilkArtNew] using hilkPos)
  have h01 :=.execBlock_append hprefix hInkBlock
  have h02 :=.execBlock_append h01 hArtBlock
  have h03 :=.execBlock_append h02 hIlkBlock
  have hDtab : ExecBlock config { contract := contract, locals := localsIlk } evm3
      (checkedMulSignedInto "dtab" (.storage (ilksF (.var "i") "rate")) (.var "dart"))
      .reverted := by
    simpa [evm0, evm1, evm2, evm3, localsIlk, urnInkNew, urnArtNew, ilkArtNew]
      using hDtabRevert
  have h04 :=.execBlock_append h03 hDtab
  have hblock :=.execBlock_append_term
    (s2 :=
      checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
      checkedSubSignedInto "sinNew" (.storage (sinRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (sinRef (.var "w")) (.var "sinNew") ] ++
      checkedSubSignedInto "viceNew" (.storage viceRef) (.var "dtab") ++
      [ .assign .storage viceRef (.var "viceNew") ])
    h04 (by intro f e h; cases h)
  simpa [ExecTransitionBody, grabTransition, nonpayable, auth, evm0, evm1, evm2, evm3,
    localsInk, localsArt, localsIlk, urnInkNew, urnArtNew, ilkArtNew, List.append_assoc]
    using ExecFuncBody.execBlockRevert hblock

theorem vatGrabSourceBodyPostDtabRevertFromBlock
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwei : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hsz196 : 196 ≤ I.calldata.size)
    (hinkNeg :
      0 ≤ grabDinkInt I ∨
        (grabUrnInkNew σ I).toNat ≤
          (vatSlotWord (grabUrnInkSlot I) σ I).toNat)
    (hinkPos :
      grabDinkInt I ≤ 0 ∨
        (vatSlotWord (grabUrnInkSlot I) σ I).toNat ≤
          (grabUrnInkNew σ I).toNat)
    (hartNeg :
      0 ≤ grabDartInt I ∨
        (grabUrnArtNew σ I).toNat ≤
          (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)).toNat)
    (hartPos :
      grabDartInt I ≤ 0 ∨
        (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)).toNat ≤
          (grabUrnArtNew σ I).toNat)
    (hilkNeg :
      0 ≤ grabDartInt I ∨
        (grabIlkArtNew σ I).toNat ≤
          (solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I)).toNat)
    (hilkPos :
      grabDartInt I ≤ 0 ∨
        (solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I)).toNat ≤
          (grabIlkArtNew σ I).toNat)
    (dtab : Int)
    (hDtabOk :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
        (grabUrnInkSourceSlot I) (grabUrnInkNew σ I)
      let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
        (grabUrnArtSourceSlot I) (grabUrnArtNew σ I)
      let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
        (grabIlkArtSourceSlot I) (grabIlkArtNew σ I)
      ExecBlock config
        { contract := contract,
          locals := grabStoreIlkArtNew I (grabUrnInkNew σ I) (grabUrnArtNew σ I)
            (grabIlkArtNew σ I) } evm3
        (checkedMulSignedInto "dtab" (.storage (ilksF (.var "i") "rate")) (.var "dart"))
        (.ok
          { contract := contract,
            locals := grabStoreDtab I (grabUrnInkNew σ I) (grabUrnArtNew σ I)
              (grabIlkArtNew σ I) dtab }
          evm3))
    (hTailRevert :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
        (grabUrnInkSourceSlot I) (grabUrnInkNew σ I)
      let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
        (grabUrnArtSourceSlot I) (grabUrnArtNew σ I)
      let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
        (grabIlkArtSourceSlot I) (grabIlkArtNew σ I)
      ExecBlock config
        { contract := contract,
          locals := grabStoreDtab I (grabUrnInkNew σ I) (grabUrnArtNew σ I)
            (grabIlkArtNew σ I) dtab } evm3
        (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
          (.var "dink") ++
        [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
        checkedSubSignedInto "sinNew" (.storage (sinRef (.var "w"))) (.var "dtab") ++
        [ .assign .storage (sinRef (.var "w")) (.var "sinNew") ] ++
        checkedSubSignedInto "viceNew" (.storage viceRef) (.var "dtab") ++
        [ .assign .storage viceRef (.var "viceNew") ])
        .reverted) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (grabStore I) grabTransition.body .reverted := by
  intro evm0
  let urnInkNew := grabUrnInkNew σ I
  let urnArtNew := grabUrnArtNew σ I
  let ilkArtNew := grabIlkArtNew σ I
  let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
    (grabUrnInkSourceSlot I) urnInkNew
  let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
    (grabUrnArtSourceSlot I) urnArtNew
  let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
    (grabIlkArtSourceSlot I) ilkArtNew
  let localsInk := grabStoreUrnInkNew I urnInkNew
  let localsArt := grabStoreUrnArtNew I urnInkNew urnArtNew
  let localsIlk := grabStoreIlkArtNew I urnInkNew urnArtNew ilkArtNew
  let localsDtab := grabStoreDtab I urnInkNew urnArtNew ilkArtNew dtab
  have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := grabStore I)
    (grabStore_get_wards I) hauth
  have hprefix :
      ExecBlock config { contract := contract, locals := grabStore I } evm0
        (nonpayable ++ auth) (.ok { contract := contract, locals := grabStore I } evm0) := by
    change ExecBlock config { contract := contract, locals := grabStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]
      (.ok { contract := contract, locals := grabStore I } evm0)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwei)
    exact ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ExecBlock.nil
  have hInkBlock :
      ExecBlock config { contract := contract, locals := grabStore I } evm0
        (checkedAddSignedInto "urnInkNew"
          (.storage (urnsF (.var "i") (.var "u") "ink")) (.var "dink") ++
          [ .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew") ])
        (.ok { contract := contract, locals := localsInk } evm1) := by
    exact execGrabUrnInkUpdateOk (evm := evm0) (I := I) (locals := grabStore I)
      (vatSlotWord (grabUrnInkSlot I) σ I) urnInkNew hsz196
      (grabStore_get_i I) (grabStore_get_u I) (grabStore_get_dink I)
      (grabStore_urns I)
      (by
        simpa [evm0] using
          (grabSourceLoad_urnInk (cA := cA) (gh := gh) (bl := bl)
            (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
      (by simp [urnInkNew, grabUrnInkNew, vatSlotWord])
      (by simpa [urnInkNew, vatSlotWord] using hinkNeg)
      (by simpa [urnInkNew, vatSlotWord] using hinkPos)
  have hArt_i : localsInk.get? "i" = some (grabIValue I) := by
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "i" =
      some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact grabStore_get_i I
  have hArt_u : localsInk.get? "u" = some (grabUValue I) := by
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get? "u" =
      some (grabUValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact grabStore_get_u I
  have hArt_dart : localsInk.get? "dart" = some (grabDartValue I) := by
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get?
      "dart" = some (grabDartValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact grabStore_get_dart I
  have hArt_urns : localsInk.get? "urns" = none := by
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get?
      "urns" = none
    rw [store_get_ne _ _ (by native_decide)]
    exact grabStore_urns I
  have hArtBlock :
      ExecBlock config { contract := contract, locals := localsInk } evm1
        (checkedAddSignedInto "urnArtNew"
          (.storage (urnsF (.var "i") (.var "u") "art")) (.var "dart") ++
          [ .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew") ])
        (.ok { contract := contract, locals := localsArt } evm2) := by
    exact execGrabUrnArtUpdateOk (evm := evm1) (I := I) (locals := localsInk)
      (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)) urnArtNew hsz196
      hArt_i hArt_u hArt_dart hArt_urns
      (by simpa [evm0, evm1] using
        (grabSourceLoad_urnArt_staged (cA := cA) (gh := gh) (bl := bl)
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
      (by simp [urnArtNew, grabUrnArtNew])
      (by simpa [urnArtNew] using hartNeg)
      (by simpa [urnArtNew] using hartPos)
  have hIlk_i : localsArt.get? "i" = some (grabIValue I) := by
    change ((grabStoreUrnInkNew I urnInkNew).insert "urnArtNew"
      (.int (Int.ofNat urnArtNew.toNat))).get? "i" = some (grabIValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hArt_i
  have hIlk_dart : localsArt.get? "dart" = some (grabDartValue I) := by
    change ((grabStoreUrnInkNew I urnInkNew).insert "urnArtNew"
      (.int (Int.ofNat urnArtNew.toNat))).get? "dart" = some (grabDartValue I)
    rw [store_get_ne _ _ (by native_decide)]
    exact hArt_dart
  have hIlk_ilks : localsArt.get? "ilks" = none := by
    change ((grabStoreUrnInkNew I urnInkNew).insert "urnArtNew"
      (.int (Int.ofNat urnArtNew.toNat))).get? "ilks" = none
    rw [store_get_ne _ _ (by native_decide)]
    change ((grabStore I).insert "urnInkNew" (.int (Int.ofNat urnInkNew.toNat))).get?
      "ilks" = none
    rw [store_get_ne _ _ (by native_decide)]
    simp [grabStore]
  have hIlkBlock :
      ExecBlock config { contract := contract, locals := localsArt } evm2
        (checkedAddSignedInto "ilkArtNew" (.storage (ilksF (.var "i") "Art"))
          (.var "dart") ++
          [ .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew") ])
        (.ok { contract := contract, locals := localsIlk } evm3) := by
    exact execGrabIlkArtUpdateOk (evm := evm2) (I := I) (locals := localsArt)
      (solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I)) ilkArtNew hsz196
      hIlk_i hIlk_dart hIlk_ilks
      (by simpa [evm0, evm1, evm2] using
        (grabSourceLoad_ilkArt_staged (cA := cA) (gh := gh) (bl := bl)
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196))
      (by simp [ilkArtNew, grabIlkArtNew])
      (by simpa [ilkArtNew] using hilkNeg)
      (by simpa [ilkArtNew] using hilkPos)
  have hDtab :
      ExecBlock config { contract := contract, locals := localsIlk } evm3
        (checkedMulSignedInto "dtab" (.storage (ilksF (.var "i") "rate")) (.var "dart"))
        (.ok { contract := contract, locals := localsDtab } evm3) := by
    simpa [evm0, evm1, evm2, evm3, localsIlk, localsDtab, urnInkNew, urnArtNew,
      ilkArtNew] using hDtabOk
  have hTail :
      ExecBlock config { contract := contract, locals := localsDtab } evm3
        (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
          (.var "dink") ++
        [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
        checkedSubSignedInto "sinNew" (.storage (sinRef (.var "w"))) (.var "dtab") ++
        [ .assign .storage (sinRef (.var "w")) (.var "sinNew") ] ++
        checkedSubSignedInto "viceNew" (.storage viceRef) (.var "dtab") ++
        [ .assign .storage viceRef (.var "viceNew") ])
        .reverted := by
    simpa [evm0, evm1, evm2, evm3, localsDtab, urnInkNew, urnArtNew, ilkArtNew]
      using hTailRevert
  have h01 :=.execBlock_append hprefix hInkBlock
  have h02 :=.execBlock_append h01 hArtBlock
  have h03 :=.execBlock_append h02 hIlkBlock
  have h04 :=.execBlock_append h03 hDtab
  have h05 :=.execBlock_append h04 hTail
  simpa [ExecTransitionBody, grabTransition, nonpayable, auth, evm0, evm1, evm2, evm3,
    localsInk, localsArt, localsIlk, localsDtab, urnInkNew, urnArtNew, ilkArtNew,
    List.append_assoc] using ExecFuncBody.execBlockRevert h05

theorem execGrabTailGemRevertFromBlock {evm : EVM.State}
    {locals : Store}
    (hGem :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
          (.var "dink"))
        .reverted) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
      checkedSubSignedInto "sinNew" (.storage (sinRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (sinRef (.var "w")) (.var "sinNew") ] ++
      checkedSubSignedInto "viceNew" (.storage viceRef) (.var "dtab") ++
      [ .assign .storage viceRef (.var "viceNew") ])
      .reverted := by
  have h :=.execBlock_append_term
    (s2 :=
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
      checkedSubSignedInto "sinNew" (.storage (sinRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (sinRef (.var "w")) (.var "sinNew") ] ++
      checkedSubSignedInto "viceNew" (.storage viceRef) (.var "dtab") ++
      [ .assign .storage viceRef (.var "viceNew") ])
    hGem (by intro f e h; cases h)
  simpa [List.append_assoc] using h

theorem execGrabTailSinRevertFromBlock {evm evm4 : EVM.State}
    {locals localsGem : Store}
    (hGem :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
          (.var "dink") ++
        [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ])
        (.ok { contract := contract, locals := localsGem } evm4))
    (hSin :
      ExecBlock config { contract := contract, locals := localsGem } evm4
        (checkedSubSignedInto "sinNew" (.storage (sinRef (.var "w"))) (.var "dtab"))
        .reverted) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
      checkedSubSignedInto "sinNew" (.storage (sinRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (sinRef (.var "w")) (.var "sinNew") ] ++
      checkedSubSignedInto "viceNew" (.storage viceRef) (.var "dtab") ++
      [ .assign .storage viceRef (.var "viceNew") ])
      .reverted := by
  have h01 :=.execBlock_append hGem hSin
  have h :=.execBlock_append_term
    (s2 :=
      [ .assign .storage (sinRef (.var "w")) (.var "sinNew") ] ++
      checkedSubSignedInto "viceNew" (.storage viceRef) (.var "dtab") ++
      [ .assign .storage viceRef (.var "viceNew") ])
    h01 (by intro f e h; cases h)
  simpa [List.append_assoc] using h

theorem execGrabTailViceRevertFromBlock {evm evm4 evm5 : EVM.State}
    {locals localsGem localsSin : Store}
    (hGem :
      ExecBlock config { contract := contract, locals := locals } evm
        (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
          (.var "dink") ++
        [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ])
        (.ok { contract := contract, locals := localsGem } evm4))
    (hSin :
      ExecBlock config { contract := contract, locals := localsGem } evm4
        (checkedSubSignedInto "sinNew" (.storage (sinRef (.var "w"))) (.var "dtab") ++
        [ .assign .storage (sinRef (.var "w")) (.var "sinNew") ])
        (.ok { contract := contract, locals := localsSin } evm5))
    (hVice :
      ExecBlock config { contract := contract, locals := localsSin } evm5
        (checkedSubSignedInto "viceNew" (.storage viceRef) (.var "dtab"))
        .reverted) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
        (.var "dink") ++
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
      checkedSubSignedInto "sinNew" (.storage (sinRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (sinRef (.var "w")) (.var "sinNew") ] ++
      checkedSubSignedInto "viceNew" (.storage viceRef) (.var "dtab") ++
      [ .assign .storage viceRef (.var "viceNew") ])
      .reverted := by
  have h01 :=.execBlock_append hGem hSin
  have h02 :=.execBlock_append h01 hVice
  have h :=.execBlock_append_term
    (s2 := [ .assign .storage viceRef (.var "viceNew") ])
    h02 (by intro f e h; cases h)
  simpa [List.append_assoc] using h

theorem vatGrabSourceBodyAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I ≠ ⟨1⟩) :
    let locals := grabStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals grabTransition.body .reverted := by
  intro locals evm0
  have hguard := vatAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (grabStore I).get? "wards" = none; exact grabStore_get_wards I)
    hauth
  have hblock := nonpayableSecondRequireReverts
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (evm := evm0)
    (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
    (rest :=
      checkedAddSignedInto "urnInkNew" (.storage (urnsF (.var "i") (.var "u") "ink"))
          (.var "dink") ++
        [ .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew") ] ++
        checkedAddSignedInto "urnArtNew" (.storage (urnsF (.var "i") (.var "u") "art"))
          (.var "dart") ++
        [ .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew") ] ++
        checkedAddSignedInto "ilkArtNew" (.storage (ilksF (.var "i") "Art"))
          (.var "dart") ++
        [ .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew") ] ++
        checkedMulSignedInto "dtab" (.storage (ilksF (.var "i") "rate")) (.var "dart") ++
        checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v")))
          (.var "dink") ++
        [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew") ] ++
        checkedSubSignedInto "sinNew" (.storage (sinRef (.var "w"))) (.var "dtab") ++
        [ .assign .storage (sinRef (.var "w")) (.var "sinNew") ] ++
        checkedSubSignedInto "viceNew" (.storage viceRef) (.var "dtab") ++
        [ .assign .storage viceRef (.var "viceNew") ])
    (by simp [evm0, initState]; exact hwv)
    hguard
  simpa [ExecTransitionBody, grabTransition, nonpayable, auth, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem vatDecode_grab_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 196) :
    decodeCalldataWithMode config.abiDecodeMode (grabTransition.params.map Param.name)
      (transitionSignature grabTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["i", "u", "v", "w", "dink", "dart"]
    [bytes32, addr, addr, addr, int256, int256] I.calldata = none
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["i", "u", "v", "w", "dink", "dart"]
    [bytes32, addr, addr, addr, int256, int256] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [bytes32, addr, int256, isDynamicABIType])]
  simp only
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, addr, addr, addr, int256, int256] =
    some 192 by native_decide]
  simp only [bind, Option.bind]
  rw [if_pos (by rw [List.length_drop, htlen]; omega :
    (I.calldata.toList.drop 4).length < 192)]

theorem vatDecode_grab_ok {I : ExecutionEnv} (hsz196 : 196 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (grabTransition.params.map Param.name)
      (transitionSignature grabTransition).paramTypes I.calldata = some (grabStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["i", "u", "v", "w", "dink", "dart"]
    [bytes32, addr, addr, addr, int256, int256] I.calldata = some (grabStore I)
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["i", "u", "v", "w", "dink", "dart"]
    [bytes32, addr, addr, addr, int256, int256] I.calldata = some (grabStore I)
  rw [vatDecodeCalldata_legacyBytes32_address_address_address_int256_int256_ok
    (cd := I.calldata) (a := "i") (b := "u") (c := "v") (d := "w")
    (e := "dink") (f := "dart") hsz196]

theorem vatDispatchGrab {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 13)) :
    dispatchMsg contract I.calldata = some grabTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 13 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some grabTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, LineSelectorBytes, cageSelectorBytes,
    canSelectorBytes, daiSelectorBytes, debtSelectorBytes, denySelectorBytes,
    fileIlkSelectorBytes, fileLineSelectorBytes, fluxSelectorBytes, foldSelectorBytes,
    forkSelectorBytes, frobSelectorBytes, gemSelectorBytes, grabSelectorBytes]
  native_decide

theorem vatReachGrabBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 13)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨973⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0x7bab3f40⟩ :=
    vatSelWord_eq_of_beq I hsz 0x7b 0xab 0x3f 0x40 ⟨0x7bab3f40⟩
      (by native_decide) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlowhigh :
      UInt256.gt (armSelNat vatBytecode vatLowHighSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms272FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [hword]
      native_decide
    · rw [hword]
      native_decide
    · rw [hword]
      native_decide
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms272FirstPc 3))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vatReachArms272Body 3 (by omega) ⟨973⟩ hcode hwv hsz hsize
    hroot hlow hlowhigh heq0 htake (by jump_dest) (by native_decide)

theorem vatGrabX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz196 : 196 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨973⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4204⟩
        [grabDartWord I, grabDinkWord I, grabWMaskedWord I, grabVMaskedWord I,
          grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨973⟩) (ret := ⟨524⟩)
    (decoded := ⟨995⟩) (need := ⟨192⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz196) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.solcSixWordThreeAddressExternalLoadAndJump
    (code := vatBytecode) (decoded := ⟨995⟩) (ret := ⟨524⟩) (routine := ⟨4204⟩)
    (R := [sel]) hdecoded
    (by
      unfold solcSixWordThreeAddressExternalLoadAndJumpWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [grabDartWord, grabDinkWord, grabWMaskedWord, grabWWord,
      grabVMaskedWord, grabVWord, grabUMaskedWord, grabUWord, grabIWord]
      using hroutine⟩

theorem vatGrabX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 196)
    (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨973⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨192⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 192
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨973⟩) (ret := ⟨524⟩)
    (decoded := ⟨995⟩) (need := ⟨192⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem vatGrabBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 196)
    (hsel : selIs I (vatSelBytes 13))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨973⟩ [vatSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (vatGrabX_shortarg (g := Sat256.ofUInt256 g) hsz4 hshort hsize hreach)
    |>.reEquivDecodingFailed hcode (vatDispatchGrab hsel)
      (vatDecode_grab_none_short hsz4 hshort)

theorem vatGrabBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz196 : 196 ≤ I.calldata.size)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some grabTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (grabTransition.params.map Param.name)
        (transitionSignature grabTransition).paramTypes I.calldata = some (grabStore I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨973⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := grabStore I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hcallerWord : vatSlotWord (vatCallerWardsSlot I) σ_evm I =
      vatSlotWord (vatCallerWardsSlot I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (vatCallerWardsSlot I) ⟨0⟩
  have hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I ≠ ⟨1⟩ := by
    intro hbad
    exact hauth (by rw [hcallerWord, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals grabTransition.body .reverted := by
    simpa [evm0, locals] using
      (vatGrabSourceBodyAuthReverts (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm)
  obtain ⟨_, _, hdecoded⟩ := vatGrabX_decoded (g := Sat256.ofUInt256 g)
    hsz196 hsize hreach
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) ≠ ⟨1⟩ := by
    simpa [vatCallerWardsSlot, vatSlotWord] using hauth
  have hrev := RD.vatAuthCheckRevert
    (pc := ⟨4204⟩) (okPc := ⟨4286⟩)
    (key := grabDartWord I) (ret := grabDinkWord I)
    (R := [grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel])
    hdecoded
    (by unfold vatAuthCheckWf; repeat' first | apply And.intro | native_decide)
    (by unfold vatAuthRevertTailWf vatAuthTailPc; repeat' first | apply And.intro | native_decide)
    hauthSolc (by simp)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem RD.vatGrabUrnInkAddSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4286⟩
      [grabDartWord I, grabDinkWord I, grabWMaskedWord I, grabVMaskedWord I,
        grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hneg :
      UInt256.slt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (grabDinkWord I + solcSlotWord σ I (grabUrnInkSlot I))
          (solcSlotWord σ I (grabUrnInkSlot I)) = ⟨0⟩)
    (hpos :
      UInt256.sgt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (grabDinkWord I + solcSlotWord σ I (grabUrnInkSlot I))
          (solcSlotWord σ I (grabUrnInkSlot I)) = ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4343⟩
      [(grabDinkWord I + solcSlotWord σ I (grabUrnInkSlot I)), grabIlkBase I,
        grabUrnBase I, grabDartWord I, grabDinkWord I, grabWMaskedWord I,
        grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      (twoWordHashMem (grabIWord I) ⟨2⟩
        (twoWordHashMem (grabUMaskedWord I) (solcMappingSlot ⟨3⟩ (grabIWord I))
          (twoWordHashMem (grabIWord I) ⟨3⟩ mem)))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let urnsIlk := solcMappingSlot ⟨3⟩ (grabIWord I)
  let urnBase := solcMappingSlot urnsIlk (grabUMaskedWord I)
  let ilkBase := solcMappingSlot ⟨2⟩ (grabIWord I)
  let urnInkOld := solcSlotWord σ I urnBase
  have rd4287 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4289 := rd4287.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4290 := rd4289.dup7 (by native_decide) (by evm_ov)
  have rd4291 := rd4290.dup2 (by native_decide) (by evm_ov)
  have rd4292 := rd4291.mstore 0 (wordAt0Mem (grabIWord I) mem) (UInt256.ofNat 3)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd4294 := rd4292.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  have rd4296 := rd4294.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd4297 := rd4296.swap1 (by native_decide) (by evm_ov)
  have rd4298 := rd4297.dup2 (by native_decide) (by evm_ov)
  have rd4299 := rd4298.mstore 0 (twoWordHashMem (grabIWord I) ⟨3⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd4301 := rd4299.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd4302 := rd4301.dup1 (by native_decide) (by evm_ov)
  have rd4303 := rd4302.dup4 (by native_decide) (by evm_ov)
  have hurnsIlk :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (grabIWord I) ⟨3⟩ mem).readWithPadding 0 64))) =
        urnsIlk := by
    simpa [urnsIlk] using twoWordHashMem_solcMappingSlot ⟨3⟩ (grabIWord I) hmem
  have rd4304 := rd4303.keccak256 0 urnsIlk (UInt256.ofNat 3) (by native_decide)
    mem_cost hurnsIlk (by native_decide) (by evm_ov)
  have rd4306 := rd4304.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4308 := rd4306.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4310 := rd4308.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd4311 := rd4310.shl (by native_decide) (by evm_ov)
  have rd4312 := rd4311.sub (by native_decide) (by evm_ov)
  have rd4313 := rd4312.dup10 (by native_decide) (by evm_ov)
  have rd4314 := rd4313.and (by native_decide) (by evm_ov)
  have hmask :
      UInt256.land (grabUMaskedWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        grabUMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact grabUMaskedWord_clean I
  rw [hmask] at rd4314
  have rd4315 := rd4314.dup5 (by native_decide) (by evm_ov)
  have rd4316 := rd4315.mstore 0
    (wordAt0Mem (grabUMaskedWord I) (twoWordHashMem (grabIWord I) ⟨3⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4317 := rd4316.dup3 (by native_decide) (by evm_ov)
  have rd4318 := rd4317.mstore 0
    (twoWordHashMem (grabUMaskedWord I) urnsIlk
      (twoWordHashMem (grabIWord I) ⟨3⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4319 := rd4318.dup1 (by native_decide) (by evm_ov)
  have rd4320 := rd4319.dup4 (by native_decide) (by evm_ov)
  have hmemUrnsIlk : (twoWordHashMem (grabIWord I) ⟨3⟩ mem).size = 96 :=
    twoWordHashMem_size_96 (grabIWord I) ⟨3⟩ hmem
  have hurnBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (grabUMaskedWord I) urnsIlk
            (twoWordHashMem (grabIWord I) ⟨3⟩ mem)).readWithPadding 0 64))) =
        urnBase := by
    simpa [urnBase] using
      twoWordHashMem_solcMappingSlot urnsIlk (grabUMaskedWord I) hmemUrnsIlk
  have rd4321 := rd4320.keccak256 0 urnBase (UInt256.ofNat 3) (by native_decide)
    mem_cost hurnBase (by native_decide) (by evm_ov)
  have rd4322 := rd4321.dup10 (by native_decide) (by evm_ov)
  have rd4323 := rd4322.dup5 (by native_decide) (by evm_ov)
  have rd4324 := rd4323.mstore 0
    (wordAt0Mem (grabIWord I)
      (twoWordHashMem (grabUMaskedWord I) urnsIlk
        (twoWordHashMem (grabIWord I) ⟨3⟩ mem)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4326 := rd4324.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd4327 := rd4326.swap1 (by native_decide) (by evm_ov)
  have rd4328 := rd4327.swap3 (by native_decide) (by evm_ov)
  have rd4329 := rd4328.mstore 0
    (twoWordHashMem (grabIWord I) ⟨2⟩
      (twoWordHashMem (grabUMaskedWord I) urnsIlk
        (twoWordHashMem (grabIWord I) ⟨3⟩ mem)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4330 := rd4329.swap1 (by native_decide) (by evm_ov)
  have rd4331 := rd4330.swap2 (by native_decide) (by evm_ov)
  have hmemUrnBase :
      (twoWordHashMem (grabUMaskedWord I) urnsIlk
        (twoWordHashMem (grabIWord I) ⟨3⟩ mem)).size = 96 :=
    twoWordHashMem_size_96 (grabUMaskedWord I) urnsIlk hmemUrnsIlk
  have hilkBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (grabIWord I) ⟨2⟩
            (twoWordHashMem (grabUMaskedWord I) urnsIlk
              (twoWordHashMem (grabIWord I) ⟨3⟩ mem))).readWithPadding 0 64))) =
        ilkBase := by
    simpa [ilkBase] using twoWordHashMem_solcMappingSlot ⟨2⟩ (grabIWord I) hmemUrnBase
  have rd4332 := rd4331.keccak256 0 ilkBase (UInt256.ofNat 3) (by native_decide)
    mem_cost hilkBase (by native_decide) (by evm_ov)
  have rd4333 := rd4332.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4334⟩ := rd4333.sload (by native_decide) (by evm_ov)
  have hold :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD urnBase ⟨0⟩)) =
        urnInkOld := by
    simp [urnInkOld, solcSlotWord]
  rw [hold] at rd4334
  have rd4337 := rd4334.push2 ⟨4343⟩ (by native_decide) (by evm_ov)
  have rd4338 := rd4337.swap1 (by native_decide) (by evm_ov)
  have rd4339 := rd4338.dup6 (by native_decide) (by evm_ov)
  have rd4342 := rd4339.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd4342.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd4343⟩ := RD.vatSignedAddOk
    (x := urnInkOld) (y := grabDinkWord I) (ret := ⟨4343⟩)
    (R := ilkBase :: urnBase :: grabDartWord I :: grabDinkWord I :: grabWMaskedWord I ::
      grabVMaskedWord I :: grabUMaskedWord I :: grabIWord I :: ⟨524⟩ :: sel :: [])
    rd6653
    (by simpa [urnInkOld, urnBase, grabUrnInkSlot, grabUrnBase] using hneg)
    (by simpa [urnInkOld, urnBase, grabUrnInkSlot, grabUrnBase] using hpos)
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [urnInkOld, urnBase, urnsIlk, ilkBase, grabUrnInkSlot, grabUrnBase, grabIlkBase]
      using rd4343⟩

theorem RD.vatGrabUrnInkAddRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4286⟩
      [grabDartWord I, grabDinkWord I, grabWMaskedWord I, grabVMaskedWord I,
        grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hfail :
      ¬ (UInt256.slt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (grabDinkWord I + solcSlotWord σ I (grabUrnInkSlot I))
          (solcSlotWord σ I (grabUrnInkSlot I)) = ⟨0⟩) ∨
      (UInt256.slt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (grabDinkWord I + solcSlotWord σ I (grabUrnInkSlot I))
          (solcSlotWord σ I (grabUrnInkSlot I)) = ⟨0⟩) ∧
        ¬ (UInt256.sgt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt (grabDinkWord I + solcSlotWord σ I (grabUrnInkSlot I))
            (solcSlotWord σ I (grabUrnInkSlot I)) = ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let urnsIlk := solcMappingSlot ⟨3⟩ (grabIWord I)
  let urnBase := solcMappingSlot urnsIlk (grabUMaskedWord I)
  let ilkBase := solcMappingSlot ⟨2⟩ (grabIWord I)
  let urnInkOld := solcSlotWord σ I urnBase
  have rd4287 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4289 := rd4287.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4290 := rd4289.dup7 (by native_decide) (by evm_ov)
  have rd4291 := rd4290.dup2 (by native_decide) (by evm_ov)
  have rd4292 := rd4291.mstore 0 (wordAt0Mem (grabIWord I) mem) (UInt256.ofNat 3)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd4294 := rd4292.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  have rd4296 := rd4294.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd4297 := rd4296.swap1 (by native_decide) (by evm_ov)
  have rd4298 := rd4297.dup2 (by native_decide) (by evm_ov)
  have rd4299 := rd4298.mstore 0 (twoWordHashMem (grabIWord I) ⟨3⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd4301 := rd4299.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd4302 := rd4301.dup1 (by native_decide) (by evm_ov)
  have rd4303 := rd4302.dup4 (by native_decide) (by evm_ov)
  have hurnsIlk :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (grabIWord I) ⟨3⟩ mem).readWithPadding 0 64))) =
        urnsIlk := by
    simpa [urnsIlk] using twoWordHashMem_solcMappingSlot ⟨3⟩ (grabIWord I) hmem
  have rd4304 := rd4303.keccak256 0 urnsIlk (UInt256.ofNat 3) (by native_decide)
    mem_cost hurnsIlk (by native_decide) (by evm_ov)
  have rd4306 := rd4304.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4308 := rd4306.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4310 := rd4308.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd4311 := rd4310.shl (by native_decide) (by evm_ov)
  have rd4312 := rd4311.sub (by native_decide) (by evm_ov)
  have rd4313 := rd4312.dup10 (by native_decide) (by evm_ov)
  have rd4314 := rd4313.and (by native_decide) (by evm_ov)
  have hmask :
      UInt256.land (grabUMaskedWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        grabUMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact grabUMaskedWord_clean I
  rw [hmask] at rd4314
  have rd4315 := rd4314.dup5 (by native_decide) (by evm_ov)
  have rd4316 := rd4315.mstore 0
    (wordAt0Mem (grabUMaskedWord I) (twoWordHashMem (grabIWord I) ⟨3⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4317 := rd4316.dup3 (by native_decide) (by evm_ov)
  have rd4318 := rd4317.mstore 0
    (twoWordHashMem (grabUMaskedWord I) urnsIlk
      (twoWordHashMem (grabIWord I) ⟨3⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4319 := rd4318.dup1 (by native_decide) (by evm_ov)
  have rd4320 := rd4319.dup4 (by native_decide) (by evm_ov)
  have hmemUrnsIlk : (twoWordHashMem (grabIWord I) ⟨3⟩ mem).size = 96 :=
    twoWordHashMem_size_96 (grabIWord I) ⟨3⟩ hmem
  have hurnBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (grabUMaskedWord I) urnsIlk
            (twoWordHashMem (grabIWord I) ⟨3⟩ mem)).readWithPadding 0 64))) =
        urnBase := by
    simpa [urnBase] using
      twoWordHashMem_solcMappingSlot urnsIlk (grabUMaskedWord I) hmemUrnsIlk
  have rd4321 := rd4320.keccak256 0 urnBase (UInt256.ofNat 3) (by native_decide)
    mem_cost hurnBase (by native_decide) (by evm_ov)
  have rd4322 := rd4321.dup10 (by native_decide) (by evm_ov)
  have rd4323 := rd4322.dup5 (by native_decide) (by evm_ov)
  have rd4324 := rd4323.mstore 0
    (wordAt0Mem (grabIWord I)
      (twoWordHashMem (grabUMaskedWord I) urnsIlk
        (twoWordHashMem (grabIWord I) ⟨3⟩ mem)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4326 := rd4324.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd4327 := rd4326.swap1 (by native_decide) (by evm_ov)
  have rd4328 := rd4327.swap3 (by native_decide) (by evm_ov)
  have rd4329 := rd4328.mstore 0
    (twoWordHashMem (grabIWord I) ⟨2⟩
      (twoWordHashMem (grabUMaskedWord I) urnsIlk
        (twoWordHashMem (grabIWord I) ⟨3⟩ mem)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4330 := rd4329.swap1 (by native_decide) (by evm_ov)
  have rd4331 := rd4330.swap2 (by native_decide) (by evm_ov)
  have hmemUrnBase :
      (twoWordHashMem (grabUMaskedWord I) urnsIlk
        (twoWordHashMem (grabIWord I) ⟨3⟩ mem)).size = 96 :=
    twoWordHashMem_size_96 (grabUMaskedWord I) urnsIlk hmemUrnsIlk
  have hilkBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (grabIWord I) ⟨2⟩
            (twoWordHashMem (grabUMaskedWord I) urnsIlk
              (twoWordHashMem (grabIWord I) ⟨3⟩ mem))).readWithPadding 0 64))) =
        ilkBase := by
    simpa [ilkBase] using twoWordHashMem_solcMappingSlot ⟨2⟩ (grabIWord I) hmemUrnBase
  have rd4332 := rd4331.keccak256 0 ilkBase (UInt256.ofNat 3) (by native_decide)
    mem_cost hilkBase (by native_decide) (by evm_ov)
  have rd4333 := rd4332.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4334⟩ := rd4333.sload (by native_decide) (by evm_ov)
  have hold :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD urnBase ⟨0⟩)) =
        urnInkOld := by
    simp [urnInkOld, solcSlotWord]
  rw [hold] at rd4334
  have rd4337 := rd4334.push2 ⟨4343⟩ (by native_decide) (by evm_ov)
  have rd4338 := rd4337.swap1 (by native_decide) (by evm_ov)
  have rd4339 := rd4338.dup6 (by native_decide) (by evm_ov)
  have rd4342 := rd4339.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd4342.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatSignedAddRevert
    (x := urnInkOld) (y := grabDinkWord I) (ret := ⟨4343⟩)
    (R := ilkBase :: urnBase :: grabDartWord I :: grabDinkWord I :: grabWMaskedWord I ::
      grabVMaskedWord I :: grabUMaskedWord I :: grabIWord I :: ⟨524⟩ :: sel :: [])
    rd6653
    (by simpa [urnInkOld, urnBase, grabUrnInkSlot, grabUrnBase] using hfail)
    (by simp)

theorem RD.vatGrabUrnArtAddSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel urnInkNew : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4343⟩
      [urnInkNew, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
        grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hneg :
      UInt256.slt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (grabDartWord I +
            solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnInkSlot I) urnInkNew)
              I (grabUrnArtSlot I))
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnInkSlot I) urnInkNew)
            I (grabUrnArtSlot I)) = ⟨0⟩)
    (hpos :
      UInt256.sgt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (grabDartWord I +
            solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnInkSlot I) urnInkNew)
              I (grabUrnArtSlot I))
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnInkSlot I) urnInkNew)
            I (grabUrnArtSlot I)) = ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4360⟩
      [(grabDartWord I +
          solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnInkSlot I) urnInkNew)
            I (grabUrnArtSlot I)),
        grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I, grabWMaskedWord I,
        grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (grabUrnInkSlot I) urnInkNew) k' C' := by
  let urnBase := grabUrnBase I
  let ilkBase := grabIlkBase I
  let σInk := sstoreAccountMap I.codeOwner σ (grabUrnInkSlot I) urnInkNew
  let urnArtOld := solcSlotWord σInk I (grabUrnArtSlot I)
  have rd4344 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4345 := rd4344.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4346⟩ := rd4345.sstore hperm (by native_decide) (by evm_ov)
  have rd4348 := rd4346.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4349 := rd4348.dup3 (by native_decide) (by evm_ov)
  have rd4350 := rd4349.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4351⟩ := rd4350.sload (by native_decide) (by evm_ov)
  have hrd4351' :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4351⟩
        [urnArtOld, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
          grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σInk) k' C' := by
    exact ⟨_, _, by
      simpa [urnArtOld, solcSlotWord, σInk, grabUrnArtSlot, grabUrnInkSlot] using rd4351⟩
  obtain ⟨_, _, rd4351'⟩ := hrd4351'
  have rd4354 := rd4351'.push2 ⟨4360⟩ (by native_decide) (by evm_ov)
  have rd4355 := rd4354.swap1 (by native_decide) (by evm_ov)
  have rd4356 := rd4355.dup5 (by native_decide) (by evm_ov)
  have rd4359 := rd4356.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd4359.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd4360⟩ := RD.vatSignedAddOk
    (x := urnArtOld) (y := grabDartWord I) (ret := ⟨4360⟩)
    (R := ilkBase :: urnBase :: grabDartWord I :: grabDinkWord I :: grabWMaskedWord I ::
      grabVMaskedWord I :: grabUMaskedWord I :: grabIWord I :: ⟨524⟩ :: sel :: [])
    rd6653
    (by simpa [urnArtOld, σInk, grabUrnArtSlot] using hneg)
    (by simpa [urnArtOld, σInk, grabUrnArtSlot] using hpos)
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [urnArtOld, σInk, urnBase, ilkBase, grabUrnArtSlot, grabUrnInkSlot]
      using rd4360⟩

theorem RD.vatGrabUrnArtAddRevert
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel urnInkNew : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4343⟩
      [urnInkNew, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
        grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hfail :
      ¬ (UInt256.slt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (grabDartWord I +
            solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnInkSlot I) urnInkNew)
              I (grabUrnArtSlot I))
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnInkSlot I) urnInkNew)
            I (grabUrnArtSlot I)) = ⟨0⟩) ∨
      (UInt256.slt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (grabDartWord I +
            solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnInkSlot I) urnInkNew)
              I (grabUrnArtSlot I))
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnInkSlot I) urnInkNew)
            I (grabUrnArtSlot I)) = ⟨0⟩) ∧
        ¬ (UInt256.sgt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (grabDartWord I +
              solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnInkSlot I) urnInkNew)
                I (grabUrnArtSlot I))
            (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnInkSlot I) urnInkNew)
              I (grabUrnArtSlot I)) = ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  let urnBase := grabUrnBase I
  let ilkBase := grabIlkBase I
  let σInk := sstoreAccountMap I.codeOwner σ (grabUrnInkSlot I) urnInkNew
  let urnArtOld := solcSlotWord σInk I (grabUrnArtSlot I)
  have rd4344 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4345 := rd4344.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4346⟩ := rd4345.sstore hperm (by native_decide) (by evm_ov)
  have rd4348 := rd4346.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4349 := rd4348.dup3 (by native_decide) (by evm_ov)
  have rd4350 := rd4349.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4351⟩ := rd4350.sload (by native_decide) (by evm_ov)
  have hrd4351' :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4351⟩
        [urnArtOld, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
          grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σInk) k' C' := by
    exact ⟨_, _, by
      simpa [urnArtOld, solcSlotWord, σInk, grabUrnArtSlot, grabUrnInkSlot] using rd4351⟩
  obtain ⟨_, _, rd4351'⟩ := hrd4351'
  have rd4354 := rd4351'.push2 ⟨4360⟩ (by native_decide) (by evm_ov)
  have rd4355 := rd4354.swap1 (by native_decide) (by evm_ov)
  have rd4356 := rd4355.dup5 (by native_decide) (by evm_ov)
  have rd4359 := rd4356.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd4359.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatSignedAddRevert
    (x := urnArtOld) (y := grabDartWord I) (ret := ⟨4360⟩)
    (R := ilkBase :: urnBase :: grabDartWord I :: grabDinkWord I :: grabWMaskedWord I ::
      grabVMaskedWord I :: grabUMaskedWord I :: grabIWord I :: ⟨524⟩ :: sel :: [])
    rd6653
    (by simpa [urnArtOld, σInk, grabUrnArtSlot] using hfail)
    (by simp)

theorem RD.vatGrabIlkArtAddSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel urnArtNew : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4360⟩
      [urnArtNew, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
        grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hneg :
      UInt256.slt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (grabDartWord I +
            solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnArtSlot I) urnArtNew)
              I (grabIlkArtSlot I))
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnArtSlot I) urnArtNew)
            I (grabIlkArtSlot I)) = ⟨0⟩)
    (hpos :
      UInt256.sgt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (grabDartWord I +
            solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnArtSlot I) urnArtNew)
              I (grabIlkArtSlot I))
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnArtSlot I) urnArtNew)
            I (grabIlkArtSlot I)) = ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4377⟩
      [(grabDartWord I +
          solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnArtSlot I) urnArtNew)
            I (grabIlkArtSlot I)),
        grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I, grabWMaskedWord I,
        grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (grabUrnArtSlot I) urnArtNew) k' C' := by
  let urnBase := grabUrnBase I
  let ilkBase := grabIlkBase I
  let σArt := sstoreAccountMap I.codeOwner σ (grabUrnArtSlot I) urnArtNew
  let ilkArtOld := solcSlotWord σArt I (grabIlkArtSlot I)
  have rd4361 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4363 := rd4361.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4364 := rd4363.dup4 (by native_decide) (by evm_ov)
  have rd4365 := rd4364.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4366⟩ := rd4365.sstore hperm (by native_decide) (by evm_ov)
  have hrd4366' :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4366⟩
        [grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
          grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I,
          ⟨524⟩, sel]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σArt) k' C' := by
    exact ⟨_, _, by
      simpa [σArt, grabUrnArtSlot] using rd4366⟩
  obtain ⟨_, _, rd4366'⟩ := hrd4366'
  have rd4367 := rd4366'.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4368⟩ := rd4367.sload (by native_decide) (by evm_ov)
  have hrd4368' :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4368⟩
        [ilkArtOld, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
          grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σArt) k' C' := by
    exact ⟨_, _, by
      simpa [ilkArtOld, solcSlotWord, σArt, grabIlkArtSlot, grabIlkBase] using rd4368⟩
  obtain ⟨_, _, rd4368'⟩ := hrd4368'
  have rd4371 := rd4368'.push2 ⟨4377⟩ (by native_decide) (by evm_ov)
  have rd4372 := rd4371.swap1 (by native_decide) (by evm_ov)
  have rd4373 := rd4372.dup5 (by native_decide) (by evm_ov)
  have rd4376 := rd4373.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd4376.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd4377⟩ := RD.vatSignedAddOk
    (x := ilkArtOld) (y := grabDartWord I) (ret := ⟨4377⟩)
    (R := ilkBase :: urnBase :: grabDartWord I :: grabDinkWord I :: grabWMaskedWord I ::
      grabVMaskedWord I :: grabUMaskedWord I :: grabIWord I :: ⟨524⟩ :: sel :: [])
    rd6653
    (by simpa [ilkArtOld, σArt, grabIlkArtSlot] using hneg)
    (by simpa [ilkArtOld, σArt, grabIlkArtSlot] using hpos)
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [ilkArtOld, σArt, urnBase, ilkBase, grabUrnArtSlot, grabIlkArtSlot]
      using rd4377⟩

theorem RD.vatGrabIlkArtAddRevert
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel urnArtNew : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4360⟩
      [urnArtNew, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
        grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hfail :
      ¬ (UInt256.slt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (grabDartWord I +
            solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnArtSlot I) urnArtNew)
              I (grabIlkArtSlot I))
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnArtSlot I) urnArtNew)
            I (grabIlkArtSlot I)) = ⟨0⟩) ∨
      (UInt256.slt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (grabDartWord I +
            solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnArtSlot I) urnArtNew)
              I (grabIlkArtSlot I))
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnArtSlot I) urnArtNew)
            I (grabIlkArtSlot I)) = ⟨0⟩) ∧
        ¬ (UInt256.sgt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (grabDartWord I +
              solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnArtSlot I) urnArtNew)
                I (grabIlkArtSlot I))
            (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabUrnArtSlot I) urnArtNew)
              I (grabIlkArtSlot I)) = ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  let urnBase := grabUrnBase I
  let ilkBase := grabIlkBase I
  let σArt := sstoreAccountMap I.codeOwner σ (grabUrnArtSlot I) urnArtNew
  let ilkArtOld := solcSlotWord σArt I (grabIlkArtSlot I)
  have rd4361 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4363 := rd4361.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4364 := rd4363.dup4 (by native_decide) (by evm_ov)
  have rd4365 := rd4364.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4366⟩ := rd4365.sstore hperm (by native_decide) (by evm_ov)
  have hrd4366' :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4366⟩
        [grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
          grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I,
          ⟨524⟩, sel]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σArt) k' C' := by
    exact ⟨_, _, by
      simpa [σArt, grabUrnArtSlot] using rd4366⟩
  obtain ⟨_, _, rd4366'⟩ := hrd4366'
  have rd4367 := rd4366'.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4368⟩ := rd4367.sload (by native_decide) (by evm_ov)
  have hrd4368' :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4368⟩
        [ilkArtOld, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
          grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σArt) k' C' := by
    exact ⟨_, _, by
      simpa [ilkArtOld, solcSlotWord, σArt, grabIlkArtSlot, grabIlkBase] using rd4368⟩
  obtain ⟨_, _, rd4368'⟩ := hrd4368'
  have rd4371 := rd4368'.push2 ⟨4377⟩ (by native_decide) (by evm_ov)
  have rd4372 := rd4371.swap1 (by native_decide) (by evm_ov)
  have rd4373 := rd4372.dup5 (by native_decide) (by evm_ov)
  have rd4376 := rd4373.push2 ⟨6653⟩ (by native_decide) (by evm_ov)
  have rd6653 := rd4376.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatSignedAddRevert
    (x := ilkArtOld) (y := grabDartWord I) (ret := ⟨4377⟩)
    (R := ilkBase :: urnBase :: grabDartWord I :: grabDinkWord I :: grabWMaskedWord I ::
      grabVMaskedWord I :: grabUMaskedWord I :: grabIWord I :: ⟨524⟩ :: sel :: [])
    rd6653
    (by simpa [ilkArtOld, σArt, grabIlkArtSlot] using hfail)
    (by simp)

theorem RD.vatGrabDtabMulSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel ilkArtNew : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4377⟩
      [ilkArtNew, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
        grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hmax :
      UInt256.slt
        (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabIlkArtSlot I) ilkArtNew)
          I (grabIlkRateSlot I))
        ⟨0⟩ = ⟨0⟩)
    (hmul :
      grabDartWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv
            (UInt256.mul (grabDartWord I)
              (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabIlkArtSlot I) ilkArtNew)
                I (grabIlkRateSlot I)))
            (grabDartWord I))
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabIlkArtSlot I) ilkArtNew)
            I (grabIlkRateSlot I)) ≠ ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4397⟩
      [UInt256.mul (grabDartWord I)
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabIlkArtSlot I) ilkArtNew)
            I (grabIlkRateSlot I)),
        ⟨0⟩, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
        grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (grabIlkArtSlot I) ilkArtNew) k' C' := by
  let urnBase := grabUrnBase I
  let ilkBase := grabIlkBase I
  let σIlkArt := sstoreAccountMap I.codeOwner σ (grabIlkArtSlot I) ilkArtNew
  let ilkRateOld := solcSlotWord σIlkArt I (grabIlkRateSlot I)
  have rd4378 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4379 := rd4378.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4380⟩ := rd4379.sstore hperm (by native_decide) (by evm_ov)
  have hrd4380' :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4380⟩
        [grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
          grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I,
          ⟨524⟩, sel]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σIlkArt) k' C' := by
    exact ⟨_, _, by
      simpa [σIlkArt, grabIlkArtSlot] using rd4380⟩
  obtain ⟨_, _, rd4380'⟩ := hrd4380'
  have rd4382 := rd4380'.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4383 := rd4382.dup2 (by native_decide) (by evm_ov)
  have rd4384 := rd4383.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4385⟩ := rd4384.sload (by native_decide) (by evm_ov)
  have hrd4385' :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4385⟩
        [ilkRateOld, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
          grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σIlkArt) k' C' := by
    exact ⟨_, _, by
      simpa [ilkRateOld, solcSlotWord, σIlkArt, grabIlkRateSlot, grabIlkBase]
        using rd4385⟩
  obtain ⟨_, _, rd4385'⟩ := hrd4385'
  have rd4387 := rd4385'.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4388 := rd4387.swap1 (by native_decide) (by evm_ov)
  have rd4391 := rd4388.push2 ⟨4397⟩ (by native_decide) (by evm_ov)
  have rd4392 := rd4391.swap1 (by native_decide) (by evm_ov)
  have rd4393 := rd4392.dup6 (by native_decide) (by evm_ov)
  have rd4396 := rd4393.push2 ⟨6706⟩ (by native_decide) (by evm_ov)
  have rd6706 := rd4396.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd4397⟩ := RD.vatSignedMulOk
    (x := ilkRateOld) (y := grabDartWord I) (ret := ⟨4397⟩)
    (R := ⟨0⟩ :: ilkBase :: urnBase :: grabDartWord I :: grabDinkWord I ::
      grabWMaskedWord I :: grabVMaskedWord I :: grabUMaskedWord I :: grabIWord I ::
      ⟨524⟩ :: sel :: [])
    rd6706
    (by simpa [ilkRateOld, σIlkArt, grabIlkRateSlot] using hmax)
    (by simpa [ilkRateOld, σIlkArt, grabIlkRateSlot] using hmul)
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [ilkRateOld, σIlkArt, urnBase, ilkBase, grabIlkArtSlot, grabIlkRateSlot]
      using rd4397⟩

theorem RD.vatGrabDtabMulRevert
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel ilkArtNew : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4377⟩
      [ilkArtNew, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
        grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hfail :
      ¬ UInt256.slt
        (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabIlkArtSlot I) ilkArtNew)
          I (grabIlkRateSlot I))
        ⟨0⟩ = ⟨0⟩ ∨
      UInt256.slt
        (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabIlkArtSlot I) ilkArtNew)
          I (grabIlkRateSlot I))
        ⟨0⟩ = ⟨0⟩ ∧
        ¬ (grabDartWord I = ⟨0⟩ ∨
          UInt256.eq
            (UInt256.sdiv
              (UInt256.mul (grabDartWord I)
                (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabIlkArtSlot I) ilkArtNew)
                  I (grabIlkRateSlot I)))
              (grabDartWord I))
            (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabIlkArtSlot I) ilkArtNew)
              I (grabIlkRateSlot I)) ≠ ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  let urnBase := grabUrnBase I
  let ilkBase := grabIlkBase I
  let σIlkArt := sstoreAccountMap I.codeOwner σ (grabIlkArtSlot I) ilkArtNew
  let ilkRateOld := solcSlotWord σIlkArt I (grabIlkRateSlot I)
  have rd4378 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4379 := rd4378.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4380⟩ := rd4379.sstore hperm (by native_decide) (by evm_ov)
  have hrd4380' :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4380⟩
        [grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
          grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I,
          ⟨524⟩, sel]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σIlkArt) k' C' := by
    exact ⟨_, _, by
      simpa [σIlkArt, grabIlkArtSlot] using rd4380⟩
  obtain ⟨_, _, rd4380'⟩ := hrd4380'
  have rd4382 := rd4380'.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4383 := rd4382.dup2 (by native_decide) (by evm_ov)
  have rd4384 := rd4383.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4385⟩ := rd4384.sload (by native_decide) (by evm_ov)
  have hrd4385' :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4385⟩
        [ilkRateOld, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
          grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
        mem (UInt256.ofNat 3) ByteArray.empty (cA, σIlkArt) k' C' := by
    exact ⟨_, _, by
      simpa [ilkRateOld, solcSlotWord, σIlkArt, grabIlkRateSlot, grabIlkBase]
        using rd4385⟩
  obtain ⟨_, _, rd4385'⟩ := hrd4385'
  have rd4387 := rd4385'.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4388 := rd4387.swap1 (by native_decide) (by evm_ov)
  have rd4391 := rd4388.push2 ⟨4397⟩ (by native_decide) (by evm_ov)
  have rd4392 := rd4391.swap1 (by native_decide) (by evm_ov)
  have rd4393 := rd4392.dup6 (by native_decide) (by evm_ov)
  have rd4396 := rd4393.push2 ⟨6706⟩ (by native_decide) (by evm_ov)
  have rd6706 := rd4396.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatSignedMulRevert
    (x := ilkRateOld) (y := grabDartWord I) (ret := ⟨4397⟩)
    (R := ⟨0⟩ :: ilkBase :: urnBase :: grabDartWord I :: grabDinkWord I ::
      grabWMaskedWord I :: grabVMaskedWord I :: grabUMaskedWord I :: grabIWord I ::
      ⟨524⟩ :: sel :: [])
    rd6706
    (by simpa [ilkRateOld, σIlkArt, grabIlkRateSlot] using hfail)
    (by simp)

theorem RD.vatGrabGemSubSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel dtab : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4397⟩
      [dtab, ⟨0⟩, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
        grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hpos :
      UInt256.sgt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.sub (solcSlotWord σ I (grabGemVSlot I)) (grabDinkWord I))
          (solcSlotWord σ I (grabGemVSlot I)) = ⟨0⟩)
    (hneg :
      UInt256.slt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (UInt256.sub (solcSlotWord σ I (grabGemVSlot I)) (grabDinkWord I))
          (solcSlotWord σ I (grabGemVSlot I)) = ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4445⟩
      [UInt256.sub (solcSlotWord σ I (grabGemVSlot I)) (grabDinkWord I),
        dtab, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
        grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      (twoWordHashMem (grabVMaskedWord I) (grabGemBase I)
        (twoWordHashMem (grabIWord I) ⟨4⟩ mem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let gemBase := grabGemBase I
  let gemSlot := grabGemVSlot I
  let gemOld := solcSlotWord σ I gemSlot
  have rd4398 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4400 := rd4398.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4401 := rd4400.dup11 (by native_decide) (by evm_ov)
  have rd4402 := rd4401.dup2 (by native_decide) (by evm_ov)
  have rd4403 := rd4402.mstore 0 (wordAt0Mem (grabIWord I) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4405 := rd4403.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd4407 := rd4405.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd4408 := rd4407.swap1 (by native_decide) (by evm_ov)
  have rd4409 := rd4408.dup2 (by native_decide) (by evm_ov)
  have rd4410 := rd4409.mstore 0 (twoWordHashMem (grabIWord I) ⟨4⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4412 := rd4410.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd4413 := rd4412.dup1 (by native_decide) (by evm_ov)
  have rd4414 := rd4413.dup4 (by native_decide) (by evm_ov)
  have hgemBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (grabIWord I) ⟨4⟩ mem).readWithPadding 0 64))) =
        gemBase := by
    simpa [gemBase, grabGemBase] using twoWordHashMem_solcMappingSlot ⟨4⟩ (grabIWord I) hmem
  have rd4415 := rd4414.keccak256 0 gemBase (UInt256.ofNat 3) (by native_decide)
    mem_cost hgemBase (by native_decide) (by evm_ov)
  have rd4417 := rd4415.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4419 := rd4417.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4421 := rd4419.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd4422 := rd4421.shl (by native_decide) (by evm_ov)
  have rd4423 := rd4422.sub (by native_decide) (by evm_ov)
  have rd4424 := rd4423.dup13 (by native_decide) (by evm_ov)
  have rd4425pre := rd4424.and (by native_decide) (by evm_ov)
  have hmask :
      UInt256.land (grabVMaskedWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        grabVMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact grabVMaskedWord_clean I
  rw [hmask] at rd4425pre
  have rd4426 := rd4425pre.dup5 (by native_decide) (by evm_ov)
  have rd4427 := rd4426.mstore 0
    (wordAt0Mem (grabVMaskedWord I) (twoWordHashMem (grabIWord I) ⟨4⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4428 := rd4427.swap1 (by native_decide) (by evm_ov)
  have rd4429 := rd4428.swap2 (by native_decide) (by evm_ov)
  have rd4430 := rd4429.mstore 0
    (twoWordHashMem (grabVMaskedWord I) gemBase (twoWordHashMem (grabIWord I) ⟨4⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4431 := rd4430.swap1 (by native_decide) (by evm_ov)
  have hmemGemBase : (twoWordHashMem (grabIWord I) ⟨4⟩ mem).size = 96 :=
    twoWordHashMem_size_96 (grabIWord I) ⟨4⟩ hmem
  have hgemSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (grabVMaskedWord I) gemBase
            (twoWordHashMem (grabIWord I) ⟨4⟩ mem)).readWithPadding 0 64))) =
        gemSlot := by
    simpa [gemSlot, grabGemVSlot, gemBase] using
      twoWordHashMem_solcMappingSlot gemBase (grabVMaskedWord I) hmemGemBase
  have rd4432 := rd4431.keccak256 0 gemSlot (UInt256.ofNat 3) (by native_decide)
    mem_cost hgemSlot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4433⟩ := rd4432.sload (by native_decide) (by evm_ov)
  have hrd4433' :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4433⟩
        [gemOld, dtab, ⟨0⟩, grabIlkBase I, grabUrnBase I, grabDartWord I,
          grabDinkWord I, grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I,
          grabIWord I, ⟨524⟩, sel]
        (twoWordHashMem (grabVMaskedWord I) gemBase
          (twoWordHashMem (grabIWord I) ⟨4⟩ mem))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by
      simpa [gemOld, solcSlotWord, gemSlot] using rd4433⟩
  obtain ⟨_, _, rd4433'⟩ := hrd4433'
  have rd4434 := rd4433'.swap1 (by native_decide) (by evm_ov)
  have rd4435 := rd4434.swap2 (by native_decide) (by evm_ov)
  have rd4436 := rd4435.pop (by native_decide) (by evm_ov)
  have rd4439 := rd4436.push2 ⟨4445⟩ (by native_decide) (by evm_ov)
  have rd4440 := rd4439.swap1 (by native_decide) (by evm_ov)
  have rd4441 := rd4440.dup7 (by native_decide) (by evm_ov)
  have rd4444 := rd4441.push2 ⟨6795⟩ (by native_decide) (by evm_ov)
  have rd6795 := rd4444.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd4445⟩ := RD.vatSignedSubOk
    (x := gemOld) (y := grabDinkWord I) (ret := ⟨4445⟩)
    (R := dtab :: grabIlkBase I :: grabUrnBase I :: grabDartWord I ::
      grabDinkWord I :: grabWMaskedWord I :: grabVMaskedWord I :: grabUMaskedWord I ::
      grabIWord I :: ⟨524⟩ :: sel :: [])
    rd6795
    (by simpa [gemOld, gemSlot, grabGemVSlot] using hpos)
    (by simpa [gemOld, gemSlot, grabGemVSlot] using hneg)
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [gemOld, gemSlot, gemBase, grabGemVSlot, grabGemBase] using rd4445⟩

theorem RD.vatGrabGemSubRevert
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel dtab : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4397⟩
      [dtab, ⟨0⟩, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
        grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hfail :
      ¬ (UInt256.sgt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.sub (solcSlotWord σ I (grabGemVSlot I)) (grabDinkWord I))
          (solcSlotWord σ I (grabGemVSlot I)) = ⟨0⟩) ∨
      (UInt256.sgt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.sub (solcSlotWord σ I (grabGemVSlot I)) (grabDinkWord I))
          (solcSlotWord σ I (grabGemVSlot I)) = ⟨0⟩) ∧
        ¬ (UInt256.slt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (UInt256.sub (solcSlotWord σ I (grabGemVSlot I)) (grabDinkWord I))
            (solcSlotWord σ I (grabGemVSlot I)) = ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  let gemBase := grabGemBase I
  let gemSlot := grabGemVSlot I
  let gemOld := solcSlotWord σ I gemSlot
  have rd4398 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4400 := rd4398.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4401 := rd4400.dup11 (by native_decide) (by evm_ov)
  have rd4402 := rd4401.dup2 (by native_decide) (by evm_ov)
  have rd4403 := rd4402.mstore 0 (wordAt0Mem (grabIWord I) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4405 := rd4403.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd4407 := rd4405.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd4408 := rd4407.swap1 (by native_decide) (by evm_ov)
  have rd4409 := rd4408.dup2 (by native_decide) (by evm_ov)
  have rd4410 := rd4409.mstore 0 (twoWordHashMem (grabIWord I) ⟨4⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4412 := rd4410.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd4413 := rd4412.dup1 (by native_decide) (by evm_ov)
  have rd4414 := rd4413.dup4 (by native_decide) (by evm_ov)
  have hgemBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (grabIWord I) ⟨4⟩ mem).readWithPadding 0 64))) =
        gemBase := by
    simpa [gemBase, grabGemBase] using twoWordHashMem_solcMappingSlot ⟨4⟩ (grabIWord I) hmem
  have rd4415 := rd4414.keccak256 0 gemBase (UInt256.ofNat 3) (by native_decide)
    mem_cost hgemBase (by native_decide) (by evm_ov)
  have rd4417 := rd4415.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4419 := rd4417.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4421 := rd4419.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd4422 := rd4421.shl (by native_decide) (by evm_ov)
  have rd4423 := rd4422.sub (by native_decide) (by evm_ov)
  have rd4424 := rd4423.dup13 (by native_decide) (by evm_ov)
  have rd4425pre := rd4424.and (by native_decide) (by evm_ov)
  have hmask :
      UInt256.land (grabVMaskedWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        grabVMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact grabVMaskedWord_clean I
  rw [hmask] at rd4425pre
  have rd4426 := rd4425pre.dup5 (by native_decide) (by evm_ov)
  have rd4427 := rd4426.mstore 0
    (wordAt0Mem (grabVMaskedWord I) (twoWordHashMem (grabIWord I) ⟨4⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4428 := rd4427.swap1 (by native_decide) (by evm_ov)
  have rd4429 := rd4428.swap2 (by native_decide) (by evm_ov)
  have rd4430 := rd4429.mstore 0
    (twoWordHashMem (grabVMaskedWord I) gemBase (twoWordHashMem (grabIWord I) ⟨4⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4431 := rd4430.swap1 (by native_decide) (by evm_ov)
  have hmemGemBase : (twoWordHashMem (grabIWord I) ⟨4⟩ mem).size = 96 :=
    twoWordHashMem_size_96 (grabIWord I) ⟨4⟩ hmem
  have hgemSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (grabVMaskedWord I) gemBase
            (twoWordHashMem (grabIWord I) ⟨4⟩ mem)).readWithPadding 0 64))) =
        gemSlot := by
    simpa [gemSlot, grabGemVSlot, gemBase] using
      twoWordHashMem_solcMappingSlot gemBase (grabVMaskedWord I) hmemGemBase
  have rd4432 := rd4431.keccak256 0 gemSlot (UInt256.ofNat 3) (by native_decide)
    mem_cost hgemSlot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4433⟩ := rd4432.sload (by native_decide) (by evm_ov)
  have hrd4433' :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4433⟩
        [gemOld, dtab, ⟨0⟩, grabIlkBase I, grabUrnBase I, grabDartWord I,
          grabDinkWord I, grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I,
          grabIWord I, ⟨524⟩, sel]
        (twoWordHashMem (grabVMaskedWord I) gemBase
          (twoWordHashMem (grabIWord I) ⟨4⟩ mem))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by
      simpa [gemOld, solcSlotWord, gemSlot] using rd4433⟩
  obtain ⟨_, _, rd4433'⟩ := hrd4433'
  have rd4434 := rd4433'.swap1 (by native_decide) (by evm_ov)
  have rd4435 := rd4434.swap2 (by native_decide) (by evm_ov)
  have rd4436 := rd4435.pop (by native_decide) (by evm_ov)
  have rd4439 := rd4436.push2 ⟨4445⟩ (by native_decide) (by evm_ov)
  have rd4440 := rd4439.swap1 (by native_decide) (by evm_ov)
  have rd4441 := rd4440.dup7 (by native_decide) (by evm_ov)
  have rd4444 := rd4441.push2 ⟨6795⟩ (by native_decide) (by evm_ov)
  have rd6795 := rd4444.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatSignedSubRevert
    (x := gemOld) (y := grabDinkWord I) (ret := ⟨4445⟩)
    (R := dtab :: grabIlkBase I :: grabUrnBase I :: grabDartWord I ::
      grabDinkWord I :: grabWMaskedWord I :: grabVMaskedWord I :: grabUMaskedWord I ::
      grabIWord I :: ⟨524⟩ :: sel :: [])
    rd6795
    (by simpa [gemOld, gemSlot, grabGemVSlot] using hfail)
    (by simp)

theorem RD.vatGrabSinSubSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel gemNew dtab : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4445⟩
      [gemNew, dtab, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
        grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hperm : I.perm = true)
    (hpos :
      UInt256.sgt dtab ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.sub
            (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabGemVSlot I) gemNew)
              I (grabSinSlot I))
            dtab)
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabGemVSlot I) gemNew)
            I (grabSinSlot I)) = ⟨0⟩)
    (hneg :
      UInt256.slt dtab ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (UInt256.sub
            (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabGemVSlot I) gemNew)
              I (grabSinSlot I))
            dtab)
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabGemVSlot I) gemNew)
            I (grabSinSlot I)) = ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4506⟩
      [UInt256.sub
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabGemVSlot I) gemNew)
            I (grabSinSlot I))
          dtab,
        dtab, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
        grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      (twoWordHashMem (grabWMaskedWord I) ⟨6⟩
        (twoWordHashMem (grabVMaskedWord I) (grabGemBase I)
          (twoWordHashMem (grabIWord I) ⟨4⟩ mem)))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (grabGemVSlot I) gemNew) k' C' := by
  let gemBase := grabGemBase I
  let gemSlot := grabGemVSlot I
  let σGem := sstoreAccountMap I.codeOwner σ gemSlot gemNew
  let sinOld := solcSlotWord σGem I (grabSinSlot I)
  have rd4446 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4448 := rd4446.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4449 := rd4448.dup11 (by native_decide) (by evm_ov)
  have rd4450 := rd4449.dup2 (by native_decide) (by evm_ov)
  have rd4451 := rd4450.mstore 0 (wordAt0Mem (grabIWord I) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4453 := rd4451.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd4455 := rd4453.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd4456 := rd4455.swap1 (by native_decide) (by evm_ov)
  have rd4457 := rd4456.dup2 (by native_decide) (by evm_ov)
  have rd4458 := rd4457.mstore 0 (twoWordHashMem (grabIWord I) ⟨4⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4460 := rd4458.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd4461 := rd4460.dup1 (by native_decide) (by evm_ov)
  have rd4462 := rd4461.dup4 (by native_decide) (by evm_ov)
  have hgemBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (grabIWord I) ⟨4⟩ mem).readWithPadding 0 64))) =
        gemBase := by
    simpa [gemBase, grabGemBase] using twoWordHashMem_solcMappingSlot ⟨4⟩ (grabIWord I) hmem
  have rd4463 := rd4462.keccak256 0 gemBase (UInt256.ofNat 3) (by native_decide)
    mem_cost hgemBase (by native_decide) (by evm_ov)
  have rd4465 := rd4463.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4467 := rd4465.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4469 := rd4467.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd4470 := rd4469.shl (by native_decide) (by evm_ov)
  have rd4471 := rd4470.sub (by native_decide) (by evm_ov)
  have rd4472 := rd4471.dup1 (by native_decide) (by evm_ov)
  have rd4473 := rd4472.dup14 (by native_decide) (by evm_ov)
  have rd4474pre := rd4473.and (by native_decide) (by evm_ov)
  have hmaskV :
      UInt256.land (grabVMaskedWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        grabVMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact grabVMaskedWord_clean I
  rw [hmaskV] at rd4474pre
  have rd4475 := rd4474pre.dup6 (by native_decide) (by evm_ov)
  have rd4476 := rd4475.mstore 0
    (wordAt0Mem (grabVMaskedWord I) (twoWordHashMem (grabIWord I) ⟨4⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4477 := rd4476.swap1 (by native_decide) (by evm_ov)
  have rd4478 := rd4477.dup4 (by native_decide) (by evm_ov)
  have rd4479 := rd4478.mstore 0
    (twoWordHashMem (grabVMaskedWord I) gemBase (twoWordHashMem (grabIWord I) ⟨4⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4480 := rd4479.dup2 (by native_decide) (by evm_ov)
  have rd4481 := rd4480.dup5 (by native_decide) (by evm_ov)
  have hmemGemBase : (twoWordHashMem (grabIWord I) ⟨4⟩ mem).size = 96 :=
    twoWordHashMem_size_96 (grabIWord I) ⟨4⟩ hmem
  have hgemSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (grabVMaskedWord I) gemBase
            (twoWordHashMem (grabIWord I) ⟨4⟩ mem)).readWithPadding 0 64))) =
        gemSlot := by
    simpa [gemSlot, grabGemVSlot, gemBase] using
      twoWordHashMem_solcMappingSlot gemBase (grabVMaskedWord I) hmemGemBase
  have rd4482 := rd4481.keccak256 0 gemSlot (UInt256.ofNat 3) (by native_decide)
    mem_cost hgemSlot (by native_decide) (by evm_ov)
  have rd4483 := rd4482.swap5 (by native_decide) (by evm_ov)
  have rd4484 := rd4483.swap1 (by native_decide) (by evm_ov)
  have rd4485 := rd4484.swap5 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4486⟩ := rd4485.sstore hperm (by native_decide) (by evm_ov)
  have hrd4486' :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4486⟩
        [⟨64⟩, ⟨32⟩, ⟨0⟩,
          UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩,
          dtab, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
          grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I,
          ⟨524⟩, sel]
        (twoWordHashMem (grabVMaskedWord I) gemBase
          (twoWordHashMem (grabIWord I) ⟨4⟩ mem))
        (UInt256.ofNat 3) ByteArray.empty (cA, σGem) k' C' := by
    exact ⟨_, _, by
      simpa [σGem, gemSlot, grabGemVSlot, gemBase, grabGemBase] using rd4486⟩
  obtain ⟨_, _, rd4486'⟩ := hrd4486'
  have rd4487 := rd4486'.swap3 (by native_decide) (by evm_ov)
  have rd4488 := rd4487.dup10 (by native_decide) (by evm_ov)
  have rd4489pre := rd4488.and (by native_decide) (by evm_ov)
  have hmaskW :
      UInt256.land (grabWMaskedWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        grabWMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact grabWMaskedWord_clean I
  rw [hmaskW] at rd4489pre
  have rd4490 := rd4489pre.dup3 (by native_decide) (by evm_ov)
  have rd4491 := rd4490.mstore 0
    (wordAt0Mem (grabWMaskedWord I)
      (twoWordHashMem (grabVMaskedWord I) gemBase
        (twoWordHashMem (grabIWord I) ⟨4⟩ mem)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4493 := rd4491.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  have rd4494 := rd4493.swap1 (by native_decide) (by evm_ov)
  have rd4495 := rd4494.mstore 0
    (twoWordHashMem (grabWMaskedWord I) ⟨6⟩
      (twoWordHashMem (grabVMaskedWord I) gemBase
        (twoWordHashMem (grabIWord I) ⟨4⟩ mem)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have hmemGemSlot :
      (twoWordHashMem (grabVMaskedWord I) gemBase
        (twoWordHashMem (grabIWord I) ⟨4⟩ mem)).size = 96 :=
    twoWordHashMem_size_96 (grabVMaskedWord I) gemBase hmemGemBase
  have hsinSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (grabWMaskedWord I) ⟨6⟩
            (twoWordHashMem (grabVMaskedWord I) gemBase
              (twoWordHashMem (grabIWord I) ⟨4⟩ mem))).readWithPadding 0 64))) =
        grabSinSlot I := by
    simpa [grabSinSlot] using
      twoWordHashMem_solcMappingSlot ⟨6⟩ (grabWMaskedWord I) hmemGemSlot
  have rd4496 := rd4495.keccak256 0 (grabSinSlot I) (UInt256.ofNat 3)
    (by native_decide) mem_cost hsinSlot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4497⟩ := rd4496.sload (by native_decide) (by evm_ov)
  have hrd4497' :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4497⟩
        [sinOld, dtab, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
          grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
        (twoWordHashMem (grabWMaskedWord I) ⟨6⟩
          (twoWordHashMem (grabVMaskedWord I) gemBase
            (twoWordHashMem (grabIWord I) ⟨4⟩ mem)))
        (UInt256.ofNat 3) ByteArray.empty (cA, σGem) k' C' := by
    exact ⟨_, _, by
      simpa [sinOld, solcSlotWord, σGem, gemSlot, grabSinSlot] using rd4497⟩
  obtain ⟨_, _, rd4497'⟩ := hrd4497'
  have rd4500 := rd4497'.push2 ⟨4506⟩ (by native_decide) (by evm_ov)
  have rd4501 := rd4500.swap1 (by native_decide) (by evm_ov)
  have rd4502 := rd4501.dup3 (by native_decide) (by evm_ov)
  have rd4505 := rd4502.push2 ⟨6795⟩ (by native_decide) (by evm_ov)
  have rd6795 := rd4505.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd4506⟩ := RD.vatSignedSubOk
    (x := sinOld) (y := dtab) (ret := ⟨4506⟩)
    (R := dtab :: grabIlkBase I :: grabUrnBase I :: grabDartWord I ::
      grabDinkWord I :: grabWMaskedWord I :: grabVMaskedWord I :: grabUMaskedWord I ::
      grabIWord I :: ⟨524⟩ :: sel :: [])
    rd6795
    (by simpa [sinOld, σGem, gemSlot, grabSinSlot, grabGemVSlot] using hpos)
    (by simpa [sinOld, σGem, gemSlot, grabSinSlot, grabGemVSlot] using hneg)
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [sinOld, σGem, gemSlot, gemBase, grabSinSlot, grabGemVSlot, grabGemBase]
      using rd4506⟩

theorem RD.vatGrabSinSubRevert
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel gemNew dtab : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4445⟩
      [gemNew, dtab, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
        grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hperm : I.perm = true)
    (hfail :
      ¬ (UInt256.sgt dtab ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.sub
            (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabGemVSlot I) gemNew)
              I (grabSinSlot I))
            dtab)
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabGemVSlot I) gemNew)
            I (grabSinSlot I)) = ⟨0⟩) ∨
      (UInt256.sgt dtab ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.sub
            (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabGemVSlot I) gemNew)
              I (grabSinSlot I))
            dtab)
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabGemVSlot I) gemNew)
            I (grabSinSlot I)) = ⟨0⟩) ∧
        ¬ (UInt256.slt dtab ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (UInt256.sub
              (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabGemVSlot I) gemNew)
                I (grabSinSlot I))
              dtab)
            (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabGemVSlot I) gemNew)
              I (grabSinSlot I)) = ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  let gemBase := grabGemBase I
  let gemSlot := grabGemVSlot I
  let σGem := sstoreAccountMap I.codeOwner σ gemSlot gemNew
  let sinOld := solcSlotWord σGem I (grabSinSlot I)
  have rd4446 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4448 := rd4446.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4449 := rd4448.dup11 (by native_decide) (by evm_ov)
  have rd4450 := rd4449.dup2 (by native_decide) (by evm_ov)
  have rd4451 := rd4450.mstore 0 (wordAt0Mem (grabIWord I) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4453 := rd4451.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd4455 := rd4453.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd4456 := rd4455.swap1 (by native_decide) (by evm_ov)
  have rd4457 := rd4456.dup2 (by native_decide) (by evm_ov)
  have rd4458 := rd4457.mstore 0 (twoWordHashMem (grabIWord I) ⟨4⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4460 := rd4458.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd4461 := rd4460.dup1 (by native_decide) (by evm_ov)
  have rd4462 := rd4461.dup4 (by native_decide) (by evm_ov)
  have hgemBase :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (grabIWord I) ⟨4⟩ mem).readWithPadding 0 64))) =
        gemBase := by
    simpa [gemBase, grabGemBase] using twoWordHashMem_solcMappingSlot ⟨4⟩ (grabIWord I) hmem
  have rd4463 := rd4462.keccak256 0 gemBase (UInt256.ofNat 3) (by native_decide)
    mem_cost hgemBase (by native_decide) (by evm_ov)
  have rd4465 := rd4463.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4467 := rd4465.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4469 := rd4467.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd4470 := rd4469.shl (by native_decide) (by evm_ov)
  have rd4471 := rd4470.sub (by native_decide) (by evm_ov)
  have rd4472 := rd4471.dup1 (by native_decide) (by evm_ov)
  have rd4473 := rd4472.dup14 (by native_decide) (by evm_ov)
  have rd4474pre := rd4473.and (by native_decide) (by evm_ov)
  have hmaskV :
      UInt256.land (grabVMaskedWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        grabVMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact grabVMaskedWord_clean I
  rw [hmaskV] at rd4474pre
  have rd4475 := rd4474pre.dup6 (by native_decide) (by evm_ov)
  have rd4476 := rd4475.mstore 0
    (wordAt0Mem (grabVMaskedWord I) (twoWordHashMem (grabIWord I) ⟨4⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4477 := rd4476.swap1 (by native_decide) (by evm_ov)
  have rd4478 := rd4477.dup4 (by native_decide) (by evm_ov)
  have rd4479 := rd4478.mstore 0
    (twoWordHashMem (grabVMaskedWord I) gemBase (twoWordHashMem (grabIWord I) ⟨4⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4480 := rd4479.dup2 (by native_decide) (by evm_ov)
  have rd4481 := rd4480.dup5 (by native_decide) (by evm_ov)
  have hmemGemBase : (twoWordHashMem (grabIWord I) ⟨4⟩ mem).size = 96 :=
    twoWordHashMem_size_96 (grabIWord I) ⟨4⟩ hmem
  have hgemSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (grabVMaskedWord I) gemBase
            (twoWordHashMem (grabIWord I) ⟨4⟩ mem)).readWithPadding 0 64))) =
        gemSlot := by
    simpa [gemSlot, grabGemVSlot, gemBase] using
      twoWordHashMem_solcMappingSlot gemBase (grabVMaskedWord I) hmemGemBase
  have rd4482 := rd4481.keccak256 0 gemSlot (UInt256.ofNat 3) (by native_decide)
    mem_cost hgemSlot (by native_decide) (by evm_ov)
  have rd4483 := rd4482.swap5 (by native_decide) (by evm_ov)
  have rd4484 := rd4483.swap1 (by native_decide) (by evm_ov)
  have rd4485 := rd4484.swap5 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4486⟩ := rd4485.sstore hperm (by native_decide) (by evm_ov)
  have hrd4486' :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4486⟩
        [⟨64⟩, ⟨32⟩, ⟨0⟩,
          UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩,
          dtab, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
          grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I,
          ⟨524⟩, sel]
        (twoWordHashMem (grabVMaskedWord I) gemBase
          (twoWordHashMem (grabIWord I) ⟨4⟩ mem))
        (UInt256.ofNat 3) ByteArray.empty (cA, σGem) k' C' := by
    exact ⟨_, _, by
      simpa [σGem, gemSlot, grabGemVSlot, gemBase, grabGemBase] using rd4486⟩
  obtain ⟨_, _, rd4486'⟩ := hrd4486'
  have rd4487 := rd4486'.swap3 (by native_decide) (by evm_ov)
  have rd4488 := rd4487.dup10 (by native_decide) (by evm_ov)
  have rd4489pre := rd4488.and (by native_decide) (by evm_ov)
  have hmaskW :
      UInt256.land (grabWMaskedWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        grabWMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact grabWMaskedWord_clean I
  rw [hmaskW] at rd4489pre
  have rd4490 := rd4489pre.dup3 (by native_decide) (by evm_ov)
  have rd4491 := rd4490.mstore 0
    (wordAt0Mem (grabWMaskedWord I)
      (twoWordHashMem (grabVMaskedWord I) gemBase
        (twoWordHashMem (grabIWord I) ⟨4⟩ mem)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4493 := rd4491.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  have rd4494 := rd4493.swap1 (by native_decide) (by evm_ov)
  have rd4495 := rd4494.mstore 0
    (twoWordHashMem (grabWMaskedWord I) ⟨6⟩
      (twoWordHashMem (grabVMaskedWord I) gemBase
        (twoWordHashMem (grabIWord I) ⟨4⟩ mem)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have hmemGemSlot :
      (twoWordHashMem (grabVMaskedWord I) gemBase
        (twoWordHashMem (grabIWord I) ⟨4⟩ mem)).size = 96 :=
    twoWordHashMem_size_96 (grabVMaskedWord I) gemBase hmemGemBase
  have hsinSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (grabWMaskedWord I) ⟨6⟩
            (twoWordHashMem (grabVMaskedWord I) gemBase
              (twoWordHashMem (grabIWord I) ⟨4⟩ mem))).readWithPadding 0 64))) =
        grabSinSlot I := by
    simpa [grabSinSlot] using
      twoWordHashMem_solcMappingSlot ⟨6⟩ (grabWMaskedWord I) hmemGemSlot
  have rd4496 := rd4495.keccak256 0 (grabSinSlot I) (UInt256.ofNat 3)
    (by native_decide) mem_cost hsinSlot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4497⟩ := rd4496.sload (by native_decide) (by evm_ov)
  have hrd4497' :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4497⟩
        [sinOld, dtab, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
          grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
        (twoWordHashMem (grabWMaskedWord I) ⟨6⟩
          (twoWordHashMem (grabVMaskedWord I) gemBase
            (twoWordHashMem (grabIWord I) ⟨4⟩ mem)))
        (UInt256.ofNat 3) ByteArray.empty (cA, σGem) k' C' := by
    exact ⟨_, _, by
      simpa [sinOld, solcSlotWord, σGem, gemSlot, grabSinSlot] using rd4497⟩
  obtain ⟨_, _, rd4497'⟩ := hrd4497'
  have rd4500 := rd4497'.push2 ⟨4506⟩ (by native_decide) (by evm_ov)
  have rd4501 := rd4500.swap1 (by native_decide) (by evm_ov)
  have rd4502 := rd4501.dup3 (by native_decide) (by evm_ov)
  have rd4505 := rd4502.push2 ⟨6795⟩ (by native_decide) (by evm_ov)
  have rd6795 := rd4505.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatSignedSubRevert
    (x := sinOld) (y := dtab) (ret := ⟨4506⟩)
    (R := dtab :: grabIlkBase I :: grabUrnBase I :: grabDartWord I ::
      grabDinkWord I :: grabWMaskedWord I :: grabVMaskedWord I :: grabUMaskedWord I ::
      grabIWord I :: ⟨524⟩ :: sel :: [])
    rd6795
    (by simpa [sinOld, σGem, gemSlot, grabSinSlot, grabGemVSlot] using hfail)
    (by simp)

theorem RD.vatGrabViceSubSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel sinNew dtab : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4506⟩
      [sinNew, dtab, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
        grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hperm : I.perm = true)
    (hpos :
      UInt256.sgt dtab ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.sub
            (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabSinSlot I) sinNew)
              I ⟨8⟩)
            dtab)
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabSinSlot I) sinNew)
            I ⟨8⟩) = ⟨0⟩)
    (hneg :
      UInt256.slt dtab ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt
          (UInt256.sub
            (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabSinSlot I) sinNew)
              I ⟨8⟩)
            dtab)
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabSinSlot I) sinNew)
            I ⟨8⟩) = ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4544⟩
      [UInt256.sub
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabSinSlot I) sinNew) I ⟨8⟩)
          dtab,
        dtab, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
        grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      (twoWordHashMem (grabWMaskedWord I) ⟨6⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (grabSinSlot I) sinNew) k' C' := by
  let σSin := sstoreAccountMap I.codeOwner σ (grabSinSlot I) sinNew
  let viceOld := solcSlotWord σSin I ⟨8⟩
  have rd4507 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4509 := rd4507.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4511 := rd4509.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4513 := rd4511.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd4514 := rd4513.shl (by native_decide) (by evm_ov)
  have rd4515 := rd4514.sub (by native_decide) (by evm_ov)
  have rd4516 := rd4515.dup8 (by native_decide) (by evm_ov)
  have rd4517pre := rd4516.and (by native_decide) (by evm_ov)
  have hmaskW :
      UInt256.land (grabWMaskedWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        grabWMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact grabWMaskedWord_clean I
  rw [hmaskW] at rd4517pre
  have rd4519 := rd4517pre.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4520 := rd4519.swap1 (by native_decide) (by evm_ov)
  have rd4521 := rd4520.dup2 (by native_decide) (by evm_ov)
  have rd4522 := rd4521.mstore 0
    (wordAt0Mem (grabWMaskedWord I) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4524 := rd4522.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  have rd4526 := rd4524.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd4527 := rd4526.mstore 0 (twoWordHashMem (grabWMaskedWord I) ⟨6⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4529 := rd4527.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd4530 := rd4529.swap1 (by native_decide) (by evm_ov)
  have hsinSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (grabWMaskedWord I) ⟨6⟩ mem).readWithPadding 0 64))) =
        grabSinSlot I := by
    simpa [grabSinSlot] using
      twoWordHashMem_solcMappingSlot ⟨6⟩ (grabWMaskedWord I) hmem
  have rd4531 := rd4530.keccak256 0 (grabSinSlot I) (UInt256.ofNat 3)
    (by native_decide) mem_cost hsinSlot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4532⟩ := rd4531.sstore hperm (by native_decide) (by evm_ov)
  have hrd4532' :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4532⟩
        [dtab, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
          grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
        (twoWordHashMem (grabWMaskedWord I) ⟨6⟩ mem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σSin) k' C' := by
    exact ⟨_, _, by
      simpa [σSin, grabSinSlot] using rd4532⟩
  obtain ⟨_, _, rd4532'⟩ := hrd4532'
  have rd4534 := rd4532'.push1 ⟨8⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4535⟩ := rd4534.sload (by native_decide) (by evm_ov)
  have hrd4535' :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4535⟩
        [viceOld, dtab, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
          grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
        (twoWordHashMem (grabWMaskedWord I) ⟨6⟩ mem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σSin) k' C' := by
    exact ⟨_, _, by
      simpa [viceOld, solcSlotWord, σSin] using rd4535⟩
  obtain ⟨_, _, rd4535'⟩ := hrd4535'
  have rd4538 := rd4535'.push2 ⟨4544⟩ (by native_decide) (by evm_ov)
  have rd4539 := rd4538.swap1 (by native_decide) (by evm_ov)
  have rd4540 := rd4539.dup3 (by native_decide) (by evm_ov)
  have rd4543 := rd4540.push2 ⟨6795⟩ (by native_decide) (by evm_ov)
  have rd6795 := rd4543.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd4544⟩ := RD.vatSignedSubOk
    (x := viceOld) (y := dtab) (ret := ⟨4544⟩)
    (R := dtab :: grabIlkBase I :: grabUrnBase I :: grabDartWord I ::
      grabDinkWord I :: grabWMaskedWord I :: grabVMaskedWord I :: grabUMaskedWord I ::
      grabIWord I :: ⟨524⟩ :: sel :: [])
    rd6795
    (by simpa [viceOld, σSin, grabSinSlot] using hpos)
    (by simpa [viceOld, σSin, grabSinSlot] using hneg)
    (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [viceOld, σSin, grabSinSlot] using rd4544⟩

theorem RD.vatGrabViceSubRevert
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel sinNew dtab : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4506⟩
      [sinNew, dtab, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
        grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hperm : I.perm = true)
    (hfail :
      ¬ (UInt256.sgt dtab ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.sub
            (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabSinSlot I) sinNew)
              I ⟨8⟩)
            dtab)
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabSinSlot I) sinNew)
            I ⟨8⟩) = ⟨0⟩) ∨
      (UInt256.sgt dtab ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt
          (UInt256.sub
            (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabSinSlot I) sinNew)
              I ⟨8⟩)
            dtab)
          (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabSinSlot I) sinNew)
            I ⟨8⟩) = ⟨0⟩) ∧
        ¬ (UInt256.slt dtab ⟨0⟩ = ⟨0⟩ ∨
          UInt256.lt
            (UInt256.sub
              (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabSinSlot I) sinNew)
                I ⟨8⟩)
              dtab)
            (solcSlotWord (sstoreAccountMap I.codeOwner σ (grabSinSlot I) sinNew)
              I ⟨8⟩) = ⟨0⟩)) :
    RDrev vatBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  let σSin := sstoreAccountMap I.codeOwner σ (grabSinSlot I) sinNew
  let viceOld := solcSlotWord σSin I ⟨8⟩
  have rd4507 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4509 := rd4507.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4511 := rd4509.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4513 := rd4511.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd4514 := rd4513.shl (by native_decide) (by evm_ov)
  have rd4515 := rd4514.sub (by native_decide) (by evm_ov)
  have rd4516 := rd4515.dup8 (by native_decide) (by evm_ov)
  have rd4517pre := rd4516.and (by native_decide) (by evm_ov)
  have hmaskW :
      UInt256.land (grabWMaskedWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        grabWMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact grabWMaskedWord_clean I
  rw [hmaskW] at rd4517pre
  have rd4519 := rd4517pre.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd4520 := rd4519.swap1 (by native_decide) (by evm_ov)
  have rd4521 := rd4520.dup2 (by native_decide) (by evm_ov)
  have rd4522 := rd4521.mstore 0
    (wordAt0Mem (grabWMaskedWord I) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4524 := rd4522.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  have rd4526 := rd4524.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd4527 := rd4526.mstore 0 (twoWordHashMem (grabWMaskedWord I) ⟨6⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd4529 := rd4527.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd4530 := rd4529.swap1 (by native_decide) (by evm_ov)
  have hsinSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (grabWMaskedWord I) ⟨6⟩ mem).readWithPadding 0 64))) =
        grabSinSlot I := by
    simpa [grabSinSlot] using
      twoWordHashMem_solcMappingSlot ⟨6⟩ (grabWMaskedWord I) hmem
  have rd4531 := rd4530.keccak256 0 (grabSinSlot I) (UInt256.ofNat 3)
    (by native_decide) mem_cost hsinSlot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4532⟩ := rd4531.sstore hperm (by native_decide) (by evm_ov)
  have hrd4532' :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4532⟩
        [dtab, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
          grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
        (twoWordHashMem (grabWMaskedWord I) ⟨6⟩ mem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σSin) k' C' := by
    exact ⟨_, _, by
      simpa [σSin, grabSinSlot] using rd4532⟩
  obtain ⟨_, _, rd4532'⟩ := hrd4532'
  have rd4534 := rd4532'.push1 ⟨8⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4535⟩ := rd4534.sload (by native_decide) (by evm_ov)
  have hrd4535' :
      ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4535⟩
        [viceOld, dtab, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
          grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
        (twoWordHashMem (grabWMaskedWord I) ⟨6⟩ mem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σSin) k' C' := by
    exact ⟨_, _, by
      simpa [viceOld, solcSlotWord, σSin] using rd4535⟩
  obtain ⟨_, _, rd4535'⟩ := hrd4535'
  have rd4538 := rd4535'.push2 ⟨4544⟩ (by native_decide) (by evm_ov)
  have rd4539 := rd4538.swap1 (by native_decide) (by evm_ov)
  have rd4540 := rd4539.dup3 (by native_decide) (by evm_ov)
  have rd4543 := rd4540.push2 ⟨6795⟩ (by native_decide) (by evm_ov)
  have rd6795 := rd4543.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.vatSignedSubRevert
    (x := viceOld) (y := dtab) (ret := ⟨4544⟩)
    (R := dtab :: grabIlkBase I :: grabUrnBase I :: grabDartWord I ::
      grabDinkWord I :: grabWMaskedWord I :: grabVMaskedWord I :: grabUMaskedWord I ::
      grabIWord I :: ⟨524⟩ :: sel :: [])
    rd6795
    (by simpa [viceOld, σSin, grabSinSlot] using hfail)
    (by simp)

theorem RD.vatGrabFinalizeSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel viceNew dtab : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4544⟩
      [viceNew, dtab, grabIlkBase I, grabUrnBase I, grabDartWord I, grabDinkWord I,
        grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨524⟩ [sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨8⟩ viceNew) k' C' := by
  have rd4545 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4547 := rd4545.push1 ⟨8⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4548⟩ := rd4547.sstore hperm (by native_decide) (by evm_ov)
  have rd4549 := rd4548.pop (by native_decide) (by evm_ov)
  have rd4550 := rd4549.pop (by native_decide) (by evm_ov)
  have rd4551 := rd4550.pop (by native_decide) (by evm_ov)
  have rd4552 := rd4551.pop (by native_decide) (by evm_ov)
  have rd4553 := rd4552.pop (by native_decide) (by evm_ov)
  have rd4554 := rd4553.pop (by native_decide) (by evm_ov)
  have rd4555 := rd4554.pop (by native_decide) (by evm_ov)
  have rd4556 := rd4555.pop (by native_decide) (by evm_ov)
  have rd4557 := rd4556.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa using rd4557.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem RD.vatGrabPrefixDtabSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4286⟩
      [grabDartWord I, grabDinkWord I, grabWMaskedWord I, grabVMaskedWord I,
        grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hInkNeg :
      UInt256.slt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (grabUrnInkNew σ I) (solcSlotWord σ I (grabUrnInkSlot I)) = ⟨0⟩)
    (hInkPos :
      UInt256.sgt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (grabUrnInkNew σ I) (solcSlotWord σ I (grabUrnInkSlot I)) = ⟨0⟩)
    (hUrnArtNeg :
      UInt256.slt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (grabUrnArtNew σ I)
          (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)) = ⟨0⟩)
    (hUrnArtPos :
      UInt256.sgt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (grabUrnArtNew σ I)
          (solcSlotWord (grabAfterUrnInk σ I) I (grabUrnArtSlot I)) = ⟨0⟩)
    (hIlkArtNeg :
      UInt256.slt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.gt (grabIlkArtNew σ I)
          (solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I)) = ⟨0⟩)
    (hIlkArtPos :
      UInt256.sgt (grabDartWord I) ⟨0⟩ = ⟨0⟩ ∨
        UInt256.lt (grabIlkArtNew σ I)
          (solcSlotWord (grabAfterUrnArt σ I) I (grabIlkArtSlot I)) = ⟨0⟩)
    (hDtabMax :
      UInt256.slt
        (solcSlotWord (grabAfterIlkArt σ I) I (grabIlkRateSlot I)) ⟨0⟩ = ⟨0⟩)
    (hDtabMul :
      grabDartWord I = ⟨0⟩ ∨
        UInt256.eq
          (UInt256.sdiv
            (UInt256.mul (grabDartWord I)
              (solcSlotWord (grabAfterIlkArt σ I) I (grabIlkRateSlot I)))
            (grabDartWord I))
          (solcSlotWord (grabAfterIlkArt σ I) I (grabIlkRateSlot I)) ≠ ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4397⟩
      [grabDtab σ I, ⟨0⟩, grabIlkBase I, grabUrnBase I, grabDartWord I,
        grabDinkWord I, grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I,
        grabIWord I, ⟨524⟩, sel]
      (twoWordHashMem (grabIWord I) ⟨2⟩
        (twoWordHashMem (grabUMaskedWord I) (solcMappingSlot ⟨3⟩ (grabIWord I))
          (twoWordHashMem (grabIWord I) ⟨3⟩
            (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem))))
      (UInt256.ofNat 3) ByteArray.empty (cA, grabAfterIlkArt σ I) k' C' := by
  let memAuth := twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem
  let memUrn :=
    twoWordHashMem (grabIWord I) ⟨2⟩
      (twoWordHashMem (grabUMaskedWord I) (solcMappingSlot ⟨3⟩ (grabIWord I))
        (twoWordHashMem (grabIWord I) ⟨3⟩ memAuth))
  have hmemAuth : memAuth.size = 96 :=
    twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
  obtain ⟨_, _, hInk⟩ := RD.vatGrabUrnInkAddSuccess
    (h := by simpa [memAuth] using h) hmemAuth
    (by simpa [grabUrnInkNew] using hInkNeg)
    (by simpa [grabUrnInkNew] using hInkPos)
  obtain ⟨_, _, hArt⟩ := RD.vatGrabUrnArtAddSuccess
    (h := by simpa [memUrn, memAuth, grabUrnInkNew] using hInk)
    hperm
    (by simpa [grabUrnInkNew, grabAfterUrnInk, grabUrnArtNew] using hUrnArtNeg)
    (by simpa [grabUrnInkNew, grabAfterUrnInk, grabUrnArtNew] using hUrnArtPos)
  obtain ⟨_, _, hIlk⟩ := RD.vatGrabIlkArtAddSuccess
    (h := by
      simpa [memUrn, memAuth, grabUrnInkNew, grabAfterUrnInk, grabUrnArtNew]
        using hArt)
    hperm
    (by
      simpa [grabUrnInkNew, grabAfterUrnInk, grabUrnArtNew, grabAfterUrnArt,
        grabIlkArtNew] using hIlkArtNeg)
    (by
      simpa [grabUrnInkNew, grabAfterUrnInk, grabUrnArtNew, grabAfterUrnArt,
        grabIlkArtNew] using hIlkArtPos)
  obtain ⟨_, _, hDtab⟩ := RD.vatGrabDtabMulSuccess
    (h := by
      simpa [memUrn, memAuth, grabUrnInkNew, grabAfterUrnInk, grabUrnArtNew,
        grabAfterUrnArt, grabIlkArtNew] using hIlk)
    hperm
    (by
      simpa [grabUrnInkNew, grabAfterUrnInk, grabUrnArtNew, grabAfterUrnArt,
        grabIlkArtNew, grabAfterIlkArt] using hDtabMax)
    (by
      simpa [grabUrnInkNew, grabAfterUrnInk, grabUrnArtNew, grabAfterUrnArt,
        grabIlkArtNew, grabAfterIlkArt] using hDtabMul)
  exact ⟨_, _, by
    simpa [memUrn, memAuth, grabUrnInkNew, grabAfterUrnInk, grabUrnArtNew,
      grabAfterUrnArt, grabIlkArtNew, grabAfterIlkArt, grabDtab] using hDtab⟩

set_option maxHeartbeats 2000000 in
theorem RD.vatGrabGemSinSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4397⟩
      [grabDtab σ I, ⟨0⟩, grabIlkBase I, grabUrnBase I, grabDartWord I,
        grabDinkWord I, grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I,
        grabIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, grabAfterIlkArt σ I) k C)
    (hmem : mem.size = 96) (hperm : I.perm = true)
    (hGemPos : grabGemPosOk σ I) (hGemNeg : grabGemNegOk σ I)
    (hSinPos : grabSinPosOk σ I) (hSinNeg : grabSinNegOk σ I) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4506⟩
      [grabSinNew σ I, grabDtab σ I, grabIlkBase I, grabUrnBase I, grabDartWord I,
        grabDinkWord I, grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I,
        grabIWord I, ⟨524⟩, sel]
      (twoWordHashMem (grabWMaskedWord I) ⟨6⟩
        (twoWordHashMem (grabVMaskedWord I) (grabGemBase I)
          (twoWordHashMem (grabIWord I) ⟨4⟩
            (twoWordHashMem (grabVMaskedWord I) (grabGemBase I)
              (twoWordHashMem (grabIWord I) ⟨4⟩ mem)))))
      (UInt256.ofNat 3) ByteArray.empty (cA, grabAfterGem σ I) k' C' := by
  let memGem :=
    twoWordHashMem (grabVMaskedWord I) (grabGemBase I)
      (twoWordHashMem (grabIWord I) ⟨4⟩ mem)
  have hmemGem : memGem.size = 96 := by
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    exact hmem
  obtain ⟨_, _, hGem⟩ := RD.vatGrabGemSubSuccess
    (h := h) hmem
    (by change grabGemPosOk σ I; exact hGemPos)
    (by change grabGemNegOk σ I; exact hGemNeg)
  change RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4445⟩
    [grabGemNew σ I, grabDtab σ I, grabIlkBase I, grabUrnBase I, grabDartWord I,
      grabDinkWord I, grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I,
      grabIWord I, ⟨524⟩, sel]
    memGem (UInt256.ofNat 3) ByteArray.empty (cA, grabAfterIlkArt σ I) _ _ at hGem
  obtain ⟨_, _, hSin⟩ := RD.vatGrabSinSubSuccess
    (h := hGem) hmemGem hperm
    (by change grabSinPosOk σ I; exact hSinPos)
    (by change grabSinNegOk σ I; exact hSinNeg)
  exact ⟨_, _, by simpa [memGem] using hSin⟩

theorem RD.vatGrabViceFinishSuccess
    {cA gh bl σInit σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4506⟩
      [grabSinNew σ I, grabDtab σ I, grabIlkBase I, grabUrnBase I, grabDartWord I,
        grabDinkWord I, grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I,
        grabIWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, grabAfterGem σ I) k C)
    (hmem : mem.size = 96) (hperm : I.perm = true)
    (hVicePos : grabVicePosOk σ I) (hViceNeg : grabViceNegOk σ I) :
    RDret vatBytecode g (initState cA gh bl σInit σ₀ g A I)
      (cA, grabAfterVice σ I) ByteArray.empty := by
  obtain ⟨_, _, hVice⟩ := RD.vatGrabViceSubSuccess
    (h := h) hmem hperm
    (by change grabVicePosOk σ I; exact hVicePos)
    (by change grabViceNegOk σ I; exact hViceNeg)
  change RD vatBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4544⟩
    [grabViceNew σ I, grabDtab σ I, grabIlkBase I, grabUrnBase I, grabDartWord I,
      grabDinkWord I, grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I,
      grabIWord I, ⟨524⟩, sel]
    (twoWordHashMem (grabWMaskedWord I) ⟨6⟩ mem)
    (UInt256.ofNat 3) ByteArray.empty (cA, grabAfterSin σ I) _ _ at hVice
  obtain ⟨_, _, h524⟩ := RD.vatGrabFinalizeSuccess
    (h := hVice) hperm
  have h525 := h524.jumpdest (by native_decide) (by evm_ov)
  simpa [grabAfterVice] using RD.stop h525 (by native_decide) (by simp)

theorem RD.vatGrabStoreSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4286⟩
      [grabDartWord I, grabDinkWord I, grabWMaskedWord I, grabVMaskedWord I,
        grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hInkNeg : grabInkNegOk σ I) (hInkPos : grabInkPosOk σ I)
    (hUrnArtNeg : grabUrnArtNegOk σ I) (hUrnArtPos : grabUrnArtPosOk σ I)
    (hIlkArtNeg : grabIlkArtNegOk σ I) (hIlkArtPos : grabIlkArtPosOk σ I)
    (hDtabMax : grabDtabMaxOk σ I) (hDtabMul : grabDtabMulOk σ I)
    (hGemPos : grabGemPosOk σ I) (hGemNeg : grabGemNegOk σ I)
    (hSinPos : grabSinPosOk σ I) (hSinNeg : grabSinNegOk σ I)
    (hVicePos : grabVicePosOk σ I) (hViceNeg : grabViceNegOk σ I) :
    RDret vatBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, grabAfterVice σ I) ByteArray.empty := by
  let memAuth := twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem
  let memUrn :=
    twoWordHashMem (grabIWord I) ⟨2⟩
      (twoWordHashMem (grabUMaskedWord I) (solcMappingSlot ⟨3⟩ (grabIWord I))
        (twoWordHashMem (grabIWord I) ⟨3⟩ memAuth))
  let memGem :=
    twoWordHashMem (grabVMaskedWord I) (grabGemBase I)
      (twoWordHashMem (grabIWord I) ⟨4⟩ memUrn)
  let memSin :=
    twoWordHashMem (grabWMaskedWord I) ⟨6⟩
      (twoWordHashMem (grabVMaskedWord I) (grabGemBase I)
        (twoWordHashMem (grabIWord I) ⟨4⟩ memGem))
  have hmemAuth : memAuth.size = 96 :=
    twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hmemUrn : memUrn.size = 96 := by
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    exact hmemAuth
  have hmemGem : memGem.size = 96 := by
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    exact hmemUrn
  have hmemSin : memSin.size = 96 := by
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    exact hmemGem
  obtain ⟨_, _, hDtab⟩ := RD.vatGrabPrefixDtabSuccess
    (h := by simpa [memAuth] using h) hperm
    (by simpa [grabInkNegOk] using hInkNeg)
    (by simpa [grabInkPosOk] using hInkPos)
    (by simpa [grabUrnArtNegOk] using hUrnArtNeg)
    (by simpa [grabUrnArtPosOk] using hUrnArtPos)
    (by simpa [grabIlkArtNegOk] using hIlkArtNeg)
    (by simpa [grabIlkArtPosOk] using hIlkArtPos)
    (by simpa [grabDtabMaxOk] using hDtabMax)
    (by simpa [grabDtabMulOk] using hDtabMul)
  obtain ⟨_, _, hSin⟩ := RD.vatGrabGemSinSuccess
    (h := by simpa [memUrn, memAuth] using hDtab) hmemUrn hperm
    hGemPos hGemNeg hSinPos hSinNeg
  exact RD.vatGrabViceFinishSuccess
    (h := by simpa [memSin, memGem] using hSin)
    hmemSin hperm hVicePos hViceNeg

theorem vatGrabSuccessEquivFromFinalState
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some grabTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (grabTransition.params.map Param.name)
        (transitionSignature grabTransition).paramTypes I.calldata = some (grabStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz196 : 196 ≤ I.calldata.size)
    (urnInkNew urnArtNew ilkArtNew : UInt256) (dtab : Int)
    (gemNew sinNew viceNew : UInt256)
    (hInkEq : urnInkNew = grabUrnInkNew σ_solm I)
    (hArtEq : urnArtNew = grabUrnArtNew σ_solm I)
    (hIlkEq : ilkArtNew = grabIlkArtNew σ_solm I)
    (hGemEq : gemNew = grabGemNew σ_solm I)
    (hSinEq : sinNew = grabSinNew σ_solm I)
    (hViceEq : viceNew = grabViceNew σ_solm I)
    (hret : RDret vatBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (cA, grabAfterVice σ_evm I) ByteArray.empty)
    (hbody :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
        (grabUrnInkSourceSlot I) urnInkNew
      let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
        (grabUrnArtSourceSlot I) urnArtNew
      let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
        (grabIlkArtSourceSlot I) ilkArtNew
      let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
        (grabGemSourceSlot I) gemNew
      let evm5 := Solm.EVM.storageStore evm4 evm4.executionEnv.codeOwner
        (grabSinSourceSlot I) sinNew
      let evm6 := Solm.EVM.storageStore evm5 evm5.executionEnv.codeOwner
        grabViceSourceSlot viceNew
      let finalLocals :=
        grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew viceNew
      ExecTransitionBody config contract evm0 (grabStore I) grabTransition.body
        (.returned { contract := contract, locals := finalLocals } evm6 none)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
    (grabUrnInkSourceSlot I) urnInkNew
  let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
    (grabUrnArtSourceSlot I) urnArtNew
  let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
    (grabIlkArtSourceSlot I) ilkArtNew
  let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
    (grabGemSourceSlot I) gemNew
  let evm5 := Solm.EVM.storageStore evm4 evm4.executionEnv.codeOwner
    (grabSinSourceSlot I) sinNew
  let evm6 := Solm.EVM.storageStore evm5 evm5.executionEnv.codeOwner grabViceSourceSlot viceNew
  let finalLocals :=
    grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew viceNew
  have hbody' :
      ExecTransitionBody config contract evm0 (grabStore I) grabTransition.body
        (.returned { contract := contract, locals := finalLocals } evm6 none) := by
    simpa [evm0, evm1, evm2, evm3, evm4, evm5, evm6, finalLocals] using hbody
  have hcreated : (cA, grabAfterVice σ_evm I).1 = evm6.createdAccounts := by
    simpa [evm0, evm1, evm2, evm3, evm4, evm5, evm6] using
      (grabSourceFinal_createdAccounts (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        urnInkNew urnArtNew ilkArtNew gemNew sinNew viceNew)
  have hsourceAccounts :
      accountMapEquiv (grabAfterVice σ_solm I) evm6.accountMap := by
    simpa [evm0, evm1, evm2, evm3, evm4, evm5, evm6] using
      (accountMapEquiv_grabSourceFinal (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz196
        urnInkNew urnArtNew ilkArtNew gemNew sinNew viceNew hInkEq hArtEq hIlkEq hGemEq
        hSinEq hViceEq)
  have hruntimeAccounts :
      accountMapEquiv (grabAfterVice σ_evm I) (grabAfterVice σ_solm I) :=
    accountMapEquiv_grabAfterVice hAccounts
  have haccounts : accountMapEquiv (cA, grabAfterVice σ_evm I).2 evm6.accountMap :=
    accountMapEquiv.trans hruntimeAccounts hsourceAccounts
  have henc : returnEquiv ByteArray.empty none grabTransition.returnType := by
    rw [show grabTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody' hcreated
    haccounts henc

theorem vatGrabAuthOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hdecoded : ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4204⟩
      [grabDartWord I, grabDinkWord I, grabWMaskedWord I, grabVMaskedWord I,
        grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4286⟩
      [grabDartWord I, grabDinkWord I, grabWMaskedWord I, grabVMaskedWord I,
        grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := hdecoded
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) = ⟨1⟩ := by
    simpa [vatCallerWardsSlot, vatSlotWord] using hauth
  exact RD.vatAuthCheckOk
    (code := vatBytecode) (pc := ⟨4204⟩) (okPc := ⟨4286⟩)
    (key := grabDartWord I) (ret := grabDinkWord I)
    (R := [grabWMaskedWord I, grabVMaskedWord I, grabUMaskedWord I, grabIWord I, ⟨524⟩, sel])
    hdecoded
    (by unfold vatAuthCheckWf; repeat' first | apply And.intro | native_decide)
    hauthSolc (by jump_dest) (by simp)

theorem vatGrabSuccessEquivFromSourceBodyAndRuntimeGuards
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some grabTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (grabTransition.params.map Param.name)
        (transitionSignature grabTransition).paramTypes I.calldata = some (grabStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz196 : 196 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hafterAuth : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4286⟩
      [grabDartWord I, grabDinkWord I, grabWMaskedWord I, grabVMaskedWord I,
        grabUMaskedWord I, grabIWord I, ⟨524⟩, sel]
      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hInkNeg : grabInkNegOk σ_evm I) (hInkPos : grabInkPosOk σ_evm I)
    (hUrnArtNeg : grabUrnArtNegOk σ_evm I)
    (hUrnArtPos : grabUrnArtPosOk σ_evm I)
    (hIlkArtNeg : grabIlkArtNegOk σ_evm I)
    (hIlkArtPos : grabIlkArtPosOk σ_evm I)
    (hDtabMax : grabDtabMaxOk σ_evm I) (hDtabMul : grabDtabMulOk σ_evm I)
    (hGemPos : grabGemPosOk σ_evm I) (hGemNeg : grabGemNegOk σ_evm I)
    (hSinPos : grabSinPosOk σ_evm I) (hSinNeg : grabSinNegOk σ_evm I)
    (hVicePos : grabVicePosOk σ_evm I) (hViceNeg : grabViceNegOk σ_evm I)
    (dtab : Int)
    (hbody :
      let urnInkNew := grabUrnInkNew σ_solm I
      let urnArtNew := grabUrnArtNew σ_solm I
      let ilkArtNew := grabIlkArtNew σ_solm I
      let gemNew := grabGemNew σ_solm I
      let sinNew := grabSinNew σ_solm I
      let viceNew := grabViceNew σ_solm I
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
        (grabUrnInkSourceSlot I) urnInkNew
      let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
        (grabUrnArtSourceSlot I) urnArtNew
      let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner
        (grabIlkArtSourceSlot I) ilkArtNew
      let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
        (grabGemSourceSlot I) gemNew
      let evm5 := Solm.EVM.storageStore evm4 evm4.executionEnv.codeOwner
        (grabSinSourceSlot I) sinNew
      let evm6 := Solm.EVM.storageStore evm5 evm5.executionEnv.codeOwner
        grabViceSourceSlot viceNew
      let finalLocals :=
        grabStoreViceNew I urnInkNew urnArtNew ilkArtNew dtab gemNew sinNew viceNew
      ExecTransitionBody config contract evm0 (grabStore I) grabTransition.body
        (.returned { contract := contract, locals := finalLocals } evm6 none)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, hafterAuth⟩ := hafterAuth
  have hret : RDret vatBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (cA, grabAfterVice σ_evm I) ByteArray.empty :=
    RD.vatGrabStoreSuccess (h := hafterAuth) hperm hInkNeg hInkPos hUrnArtNeg
      hUrnArtPos hIlkArtNeg hIlkArtPos hDtabMax hDtabMul hGemPos hGemNeg hSinPos
      hSinNeg hVicePos hViceNeg
  exact vatGrabSuccessEquivFromFinalState hcode hdispatch hdecode hAccounts hsz196
    (grabUrnInkNew σ_solm I) (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I)
    dtab (grabGemNew σ_solm I) (grabSinNew σ_solm I) (grabViceNew σ_solm I)
    rfl rfl rfl rfl rfl rfl hret hbody

theorem vatGrabBodyCore : VatBodyTheorem 13 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 13) rfl hsel
  have hreach := vatReachGrabBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz196 : 196 ≤ I.calldata.size
  · have hdecode := vatDecode_grab_ok (I := I) hsz196
    obtain ⟨_, _, hdecoded⟩ := vatGrabX_decoded
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hsz196 hsize hreach
    by_cases hauth : vatSlotWord (vatCallerWardsSlot I) σ_evm I = ⟨1⟩
    · obtain ⟨_, _, hafterAuth⟩ := vatGrabAuthOk
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (sel := vatSelWord I) hauth ⟨_, _, hdecoded⟩
      let dtab : Int :=
        Int.ofNat (solcSlotWord (grabAfterIlkArt σ_solm I) I (grabIlkRateSlot I)).toNat *
          grabDartInt I
      let dtabWord : UInt256 := grabDtab σ_solm I
      let evm3 :=
        grabSourceEvm3 cA gh bl σ_solm σ₀ A I g
          (grabUrnInkNew σ_solm I) (grabUrnArtNew σ_solm I)
          (grabIlkArtNew σ_solm I)
      let localsDtab :=
        (grabStoreIlkArtNew I (grabUrnInkNew σ_solm I) (grabUrnArtNew σ_solm I)
          (grabIlkArtNew σ_solm I)).insert "dtab" (.int dtab)
      have hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩ := by
        have hcallerWord : vatSlotWord (vatCallerWardsSlot I) σ_evm I =
            vatSlotWord (vatCallerWardsSlot I) σ_solm I :=
          accountMapEquiv_storage_findD hAccounts I.codeOwner (vatCallerWardsSlot I) ⟨0⟩
        simpa [hcallerWord] using hauth
      by_cases hsuccess :
          grabInkNegOk σ_evm I ∧ grabInkPosOk σ_evm I ∧
          grabUrnArtNegOk σ_evm I ∧ grabUrnArtPosOk σ_evm I ∧
          grabIlkArtNegOk σ_evm I ∧ grabIlkArtPosOk σ_evm I ∧
          grabDtabMaxOk σ_evm I ∧ grabDtabMulOk σ_evm I ∧
          grabGemPosOk σ_evm I ∧ grabGemNegOk σ_evm I ∧
          grabSinPosOk σ_evm I ∧ grabSinNegOk σ_evm I ∧
          grabVicePosOk σ_evm I ∧ grabViceNegOk σ_evm I ∧
          -((2 : Int) ^ 255) ≤ dtab ∧ dtab < (2 : Int) ^ 255 ∧
          evalExpr? config { contract := contract, locals := localsDtab } evm3
            (.binary .le (.storage (ilksF (.var "i") "rate")) (.intLit maxInt256)) =
            .ok (.bool true) ∧
          evalExpr? config { contract := contract, locals := localsDtab } evm3
            (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
              (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
                (.storage (ilksF (.var "i") "rate")))) =
            .ok (.bool true)
      · rcases hsuccess with
          ⟨hInkNeg, hInkPos, hUrnArtNeg, hUrnArtPos, hIlkArtNeg, hIlkArtPos,
            hDtabMax, hDtabMul, hGemPos, hGemNeg, hSinPos, hSinNeg, hVicePos,
            hViceNeg, hdtabLo, hdtabHi, hguardMax, hguardMul⟩
        have hdtabMod :
            dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat := by
          change
            (Int.ofNat (solcSlotWord (grabAfterIlkArt σ_solm I) I
              (grabIlkRateSlot I)).toNat * grabDartInt I) %
                (Int.ofNat EVM.wordModulus) =
              Int.ofNat
                (UInt256.mul (grabDartWord I)
                  (solcSlotWord (grabAfterIlkArt σ_solm I) I
                    (grabIlkRateSlot I))).toNat
          exact
            grabDtab_mod_word I
              (solcSlotWord (grabAfterIlkArt σ_solm I) I (grabIlkRateSlot I))
        have hbody :=
          vatGrabSourceBodySuccessFromRuntimeGuards
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hwv hauthSolm hAccounts hsz196 dtab dtabWord
            (by rfl) (by rfl) hdtabLo hdtabHi hdtabMod
            (by simpa [evm3, localsDtab] using hguardMax)
            (by simpa [evm3, localsDtab] using hguardMul)
            hInkNeg hInkPos hUrnArtNeg hUrnArtPos hIlkArtNeg hIlkArtPos
            hDtabMax hDtabMul hGemPos hGemNeg hSinPos hSinNeg hVicePos hViceNeg
        exact vatGrabSuccessEquivFromSourceBodyAndRuntimeGuards
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          (sel := vatSelWord I) hcode (vatDispatchGrab hsel) hdecode hAccounts hsz196
          hperm ⟨_, _, hafterAuth⟩ hInkNeg hInkPos hUrnArtNeg hUrnArtPos
          hIlkArtNeg hIlkArtPos hDtabMax hDtabMul hGemPos hGemNeg hSinPos hSinNeg
          hVicePos hViceNeg dtab hbody
      · by_cases hInkNeg : grabInkNegOk σ_evm I
        · by_cases hInkPos : grabInkPosOk σ_evm I
          · by_cases hUrnArtNeg : grabUrnArtNegOk σ_evm I
            · by_cases hUrnArtPos : grabUrnArtPosOk σ_evm I
              · by_cases hIlkArtNeg : grabIlkArtNegOk σ_evm I
                · by_cases hIlkArtPos : grabIlkArtPosOk σ_evm I
                  · by_cases hDtabMax : grabDtabMaxOk σ_evm I
                    · by_cases hDtabMul : grabDtabMulOk σ_evm I
                      · rcases accountMapEquiv_grabAddGuards hAccounts hInkNeg hInkPos
                            hUrnArtNeg hUrnArtPos hIlkArtNeg hIlkArtPos with
                          ⟨hInkNegS, hInkPosS, hUrnArtNegS, hUrnArtPosS,
                            hIlkArtNegS, hIlkArtPosS, hAfterIlk⟩
                        have hRateEq :
                            solcSlotWord (grabAfterIlkArt σ_evm I) I (grabIlkRateSlot I) =
                              solcSlotWord (grabAfterIlkArt σ_solm I) I
                                (grabIlkRateSlot I) :=
                          accountMapEquiv_storage_findD hAfterIlk I.codeOwner
                            (grabIlkRateSlot I) ⟨0⟩
                        have hDtabMaxS :
                            UInt256.slt
                              (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                (grabIlkRateSlot I)) ⟨0⟩ = ⟨0⟩ := by
                          simpa [grabDtabMaxOk, hRateEq] using hDtabMax
                        have hRateLowS :
                            (solcSlotWord (grabAfterIlkArt σ_solm I) I
                              (grabIlkRateSlot I)).toNat < EVM.twoPow 255 :=
                          u256_toNat_lt_sign_of_slt_zero hDtabMaxS
                        have hMulGuardEqS :
                            grabDartWord I = ⟨0⟩ ∨
                              UInt256.sdiv
                                (UInt256.mul (grabDartWord I)
                                  (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                    (grabIlkRateSlot I)))
                                (grabDartWord I) =
                              (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                (grabIlkRateSlot I)) := by
                          have hMulE :
                              grabDartWord I = ⟨0⟩ ∨
                                UInt256.eq
                                  (UInt256.sdiv
                                    (UInt256.mul (grabDartWord I)
                                      (solcSlotWord (grabAfterIlkArt σ_evm I) I
                                        (grabIlkRateSlot I)))
                                    (grabDartWord I))
                                  (solcSlotWord (grabAfterIlkArt σ_evm I) I
                                    (grabIlkRateSlot I)) ≠ ⟨0⟩ := by
                            simpa [grabDtabMulOk] using hDtabMul
                          cases hMulE with
                          | inl hzero => exact Or.inl hzero
                          | inr hne =>
                              exact Or.inr (u256_eq_ne_zero_to_eq (by
                                simpa [hRateEq] using hne))
                        have hDtabRange :=
                          grab_dtab_product_range_of_guard I
                            (rate := solcSlotWord (grabAfterIlkArt σ_solm I) I
                              (grabIlkRateSlot I))
                            hRateLowS hMulGuardEqS
                        have hdtabLo : -((2 : Int) ^ 255) ≤ dtab := by
                          change
                            -((2 : Int) ^ 255) ≤
                              Int.ofNat
                                (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                  (grabIlkRateSlot I)).toNat * grabDartInt I
                          exact hDtabRange.1
                        have hdtabHi : dtab < (2 : Int) ^ 255 := by
                          change
                            Int.ofNat
                              (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                (grabIlkRateSlot I)).toNat * grabDartInt I <
                              (2 : Int) ^ 255
                          exact hDtabRange.2
                        have hRateEval :
                            evalExpr? config { contract := contract, locals := localsDtab } evm3
                              (.storage (ilksF (.var "i") "rate")) =
                            .ok (.int (Int.ofNat
                              (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                (grabIlkRateSlot I)).toNat)) := by
                          change
                            evalExpr? config
                              { contract := contract,
                                locals := grabStoreDtab I (grabUrnInkNew σ_solm I)
                                  (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I)
                                  dtab } evm3
                              (.storage (ilksF (.var "i") "rate")) =
                            .ok (.int (Int.ofNat
                              (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                (grabIlkRateSlot I)).toNat))
                          rw [evalExpr_grab_ilk_rate_locals
                            (grabStoreDtab I (grabUrnInkNew σ_solm I)
                              (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I) dtab)
                            hsz196
                            (grabStoreDtab_get_i I (grabUrnInkNew σ_solm I)
                              (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I) dtab)
                            (grabStoreDtab_ilks I (grabUrnInkNew σ_solm I)
                              (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I) dtab)]
                          rw [grabSourceLoad_ilkRate_staged (cA := cA) (gh := gh)
                            (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
                            (I := I) (g := g) hsz196]
                        have hMaxLit :
                            evalExpr? config { contract := contract, locals := localsDtab } evm3
                              (.intLit maxInt256) = .ok (.int maxInt256) := by
                          simp [evalExpr?, pure]
                        have hguardMax :
                            evalExpr? config { contract := contract, locals := localsDtab } evm3
                              (.binary .le (.storage (ilksF (.var "i") "rate"))
                                (.intLit maxInt256)) =
                            .ok (.bool true) :=
                          vatEvalExpr_le_int_true hRateEval hMaxLit
                            (uintWordLeMaxInt256_of_slt_zero hDtabMaxS)
                        have hguardMul :
                            evalExpr? config { contract := contract, locals := localsDtab } evm3
                              (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
                                (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
                                  (.storage (ilksF (.var "i") "rate")))) =
                            .ok (.bool true) := by
                          change
                            evalExpr? config
                              { contract := contract,
                                locals := (grabStoreIlkArtNew I (grabUrnInkNew σ_solm I)
                                  (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I)).insert
                                  "dtab" (.int dtab) } evm3
                              (eitherExpr (.binary .eq (.var "dart") (.intLit 0))
                                (.binary .eq (.binary .div (.var "dtab") (.var "dart"))
                                  (.storage (ilksF (.var "i") "rate")))) =
                            .ok (.bool true)
                          by_cases hwordZero : grabDartWord I = ⟨0⟩
                          · exact
                              evalExpr_grab_dtab_mul_guard_dart_zero_true
                                (evm := evm3)
                                (locals := grabStoreIlkArtNew I (grabUrnInkNew σ_solm I)
                                  (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I))
                                I
                                (grabStoreIlkArtNew_get_dart I (grabUrnInkNew σ_solm I)
                                  (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I))
                                (grabDartInt_zero_of_word_zero I hwordZero)
                          · have hdartNe : grabDartInt I ≠ 0 :=
                              grabDartInt_ne_zero_of_word_ne I hwordZero
                            have hdiv :
                                dtab / grabDartInt I =
                                  Int.ofNat
                                    (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                      (grabIlkRateSlot I)).toNat := by
                              change
                                (Int.ofNat
                                  (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                    (grabIlkRateSlot I)).toNat * grabDartInt I) /
                                  grabDartInt I =
                                Int.ofNat
                                  (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                    (grabIlkRateSlot I)).toNat
                              exact Int.mul_ediv_cancel
                                (Int.ofNat
                                  (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                    (grabIlkRateSlot I)).toNat)
                                hdartNe
                            exact
                              evalExpr_grab_dtab_mul_guard_exact_true
                                (evm := evm3)
                                (locals := grabStoreIlkArtNew I (grabUrnInkNew σ_solm I)
                                  (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I))
                                (rate := solcSlotWord (grabAfterIlkArt σ_solm I) I
                                  (grabIlkRateSlot I))
                                I
                                (grabStoreIlkArtNew_get_dart I (grabUrnInkNew σ_solm I)
                                  (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I))
                                (by simpa using hRateEval)
                                hdartNe hdiv
                        have hdtabMod :
                            dtab % (Int.ofNat EVM.wordModulus) = Int.ofNat dtabWord.toNat := by
                          change
                            (Int.ofNat (solcSlotWord (grabAfterIlkArt σ_solm I) I
                              (grabIlkRateSlot I)).toNat * grabDartInt I) %
                                (Int.ofNat EVM.wordModulus) =
                              Int.ofNat
                                (UInt256.mul (grabDartWord I)
                                  (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                    (grabIlkRateSlot I))).toNat
                          exact
                            grabDtab_mod_word I
                              (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                (grabIlkRateSlot I))
                        have hInkGuardNeg :
                            0 ≤ grabDinkInt I ∨
                              (grabUrnInkNew σ_solm I).toNat ≤
                                (vatSlotWord (grabUrnInkSlot I) σ_solm I).toNat := by
                          exact grabDinkAddGuardNegCond (by
                            simpa [grabInkNegOk, grabUrnInkNew, vatSlotWord] using hInkNegS)
                        have hInkGuardPos :
                            grabDinkInt I ≤ 0 ∨
                              (vatSlotWord (grabUrnInkSlot I) σ_solm I).toNat ≤
                                (grabUrnInkNew σ_solm I).toNat := by
                          exact grabDinkAddGuardPosCond (by
                            simpa [grabInkPosOk, grabUrnInkNew, vatSlotWord] using hInkPosS)
                        have hArtGuardNeg :
                            0 ≤ grabDartInt I ∨
                              (grabUrnArtNew σ_solm I).toNat ≤
                                (solcSlotWord (grabAfterUrnInk σ_solm I) I
                                  (grabUrnArtSlot I)).toNat := by
                          exact grabDartAddGuardNegCond (by
                            simpa [grabUrnArtNegOk, grabUrnArtNew] using hUrnArtNegS)
                        have hArtGuardPos :
                            grabDartInt I ≤ 0 ∨
                              (solcSlotWord (grabAfterUrnInk σ_solm I) I
                                (grabUrnArtSlot I)).toNat ≤
                                (grabUrnArtNew σ_solm I).toNat := by
                          exact grabDartAddGuardPosCond (by
                            simpa [grabUrnArtPosOk, grabUrnArtNew] using hUrnArtPosS)
                        have hIlkGuardNeg :
                            0 ≤ grabDartInt I ∨
                              (grabIlkArtNew σ_solm I).toNat ≤
                                (solcSlotWord (grabAfterUrnArt σ_solm I) I
                                  (grabIlkArtSlot I)).toNat := by
                          exact grabDartAddGuardNegCond (by
                            simpa [grabIlkArtNegOk, grabIlkArtNew] using hIlkArtNegS)
                        have hIlkGuardPos :
                            grabDartInt I ≤ 0 ∨
                              (solcSlotWord (grabAfterUrnArt σ_solm I) I
                                (grabIlkArtSlot I)).toNat ≤
                                (grabIlkArtNew σ_solm I).toNat := by
                          exact grabDartAddGuardPosCond (by
                            simpa [grabIlkArtPosOk, grabIlkArtNew] using hIlkArtPosS)
                        have hDtabOk :
                            let evm0 := initState cA gh bl σ_solm σ₀
                              (Sat256.ofUInt256 g) A I
                            let evm1 := Solm.EVM.storageStore evm0
                              evm0.executionEnv.codeOwner
                              (grabUrnInkSourceSlot I) (grabUrnInkNew σ_solm I)
                            let evm2 := Solm.EVM.storageStore evm1
                              evm1.executionEnv.codeOwner
                              (grabUrnArtSourceSlot I) (grabUrnArtNew σ_solm I)
                            let evm3 := Solm.EVM.storageStore evm2
                              evm2.executionEnv.codeOwner
                              (grabIlkArtSourceSlot I) (grabIlkArtNew σ_solm I)
                            ExecBlock config
                              { contract := contract,
                                locals := grabStoreIlkArtNew I (grabUrnInkNew σ_solm I)
                                  (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I) }
                              evm3
                              (checkedMulSignedInto "dtab"
                                (.storage (ilksF (.var "i") "rate")) (.var "dart"))
                              (.ok
                                { contract := contract,
                                  locals := grabStoreDtab I (grabUrnInkNew σ_solm I)
                                    (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I) dtab }
                                evm3) := by
                          intro evm0' evm1' evm2' evm3'
                          exact execGrabDtabMulCheckedOk
                            (evm := evm3') (I := I)
                            (grabStoreIlkArtNew I (grabUrnInkNew σ_solm I)
                              (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I))
                            (solcSlotWord (grabAfterIlkArt σ_solm I) I
                              (grabIlkRateSlot I))
                            dtab hsz196
                            (grabStoreIlkArtNew_get_i I (grabUrnInkNew σ_solm I)
                              (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I))
                            (grabStoreIlkArtNew_get_dart I (grabUrnInkNew σ_solm I)
                              (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I))
                            (grabStoreIlkArtNew_ilks I (grabUrnInkNew σ_solm I)
                              (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I))
                            (by simpa [evm0', evm1', evm2', evm3'] using
                              (grabSourceLoad_ilkRate_staged (cA := cA) (gh := gh)
                                (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
                                (I := I) (g := g) hsz196))
                            (by rfl) hdtabLo hdtabHi
                            (by simpa [evm3, localsDtab, evm0', evm1', evm2', evm3']
                              using hguardMax)
                            (by simpa [evm3, localsDtab, evm0', evm1', evm2', evm3']
                              using hguardMul)
                        let memAuth := twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem
                        let memUrn :=
                          twoWordHashMem (grabIWord I) ⟨2⟩
                            (twoWordHashMem (grabUMaskedWord I)
                              (solcMappingSlot ⟨3⟩ (grabIWord I))
                              (twoWordHashMem (grabIWord I) ⟨3⟩ memAuth))
                        let memGem :=
                          twoWordHashMem (grabVMaskedWord I) (grabGemBase I)
                            (twoWordHashMem (grabIWord I) ⟨4⟩ memUrn)
                        let memSin :=
                          twoWordHashMem (grabWMaskedWord I) ⟨6⟩
                            (twoWordHashMem (grabVMaskedWord I) (grabGemBase I)
                              (twoWordHashMem (grabIWord I) ⟨4⟩ memGem))
                        have hmemAuth : memAuth.size = 96 :=
                          twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩
                            solcFreePtrMem_size
                        have hmemUrn : memUrn.size = 96 := by
                          apply twoWordHashMem_size_96
                          apply twoWordHashMem_size_96
                          apply twoWordHashMem_size_96
                          exact hmemAuth
                        have hmemGem : memGem.size = 96 := by
                          apply twoWordHashMem_size_96
                          apply twoWordHashMem_size_96
                          exact hmemUrn
                        have hmemSin : memSin.size = 96 := by
                          apply twoWordHashMem_size_96
                          apply twoWordHashMem_size_96
                          apply twoWordHashMem_size_96
                          exact hmemGem
                        obtain ⟨_, _, hDtabRD⟩ := RD.vatGrabPrefixDtabSuccess
                          (h := by simpa [memAuth] using hafterAuth) hperm
                          (by simpa [grabInkNegOk] using hInkNeg)
                          (by simpa [grabInkPosOk] using hInkPos)
                          (by simpa [grabUrnArtNegOk] using hUrnArtNeg)
                          (by simpa [grabUrnArtPosOk] using hUrnArtPos)
                          (by simpa [grabIlkArtNegOk] using hIlkArtNeg)
                          (by simpa [grabIlkArtPosOk] using hIlkArtPos)
                          (by simpa [grabDtabMaxOk] using hDtabMax)
                          (by simpa [grabDtabMulOk] using hDtabMul)
                        by_cases hGemPos : grabGemPosOk σ_evm I
                        · by_cases hGemNeg : grabGemNegOk σ_evm I
                          · by_cases hSinPos : grabSinPosOk σ_evm I
                            · by_cases hSinNeg : grabSinNegOk σ_evm I
                              · by_cases hVicePos : grabVicePosOk σ_evm I
                                · by_cases hViceNeg : grabViceNegOk σ_evm I
                                  · exact False.elim (hsuccess
                                      ⟨hInkNeg, hInkPos, hUrnArtNeg, hUrnArtPos,
                                        hIlkArtNeg, hIlkArtPos, hDtabMax, hDtabMul,
                                        hGemPos, hGemNeg, hSinPos, hSinNeg, hVicePos,
                                        hViceNeg, hdtabLo, hdtabHi, hguardMax, hguardMul⟩)
                                  · have hGemOldEq :
                                        solcSlotWord (grabAfterIlkArt σ_evm I) I
                                          (grabGemVSlot I) =
                                          solcSlotWord (grabAfterIlkArt σ_solm I) I
                                            (grabGemVSlot I) :=
                                      accountMapEquiv_storage_findD hAfterIlk I.codeOwner
                                        (grabGemVSlot I) ⟨0⟩
                                    have hGemNewEq :
                                        grabGemNew σ_evm I = grabGemNew σ_solm I := by
                                      simp [grabGemNew, hGemOldEq]
                                    have hAfterGem :
                                        accountMapEquiv (grabAfterGem σ_evm I)
                                          (grabAfterGem σ_solm I) := by
                                      simp [grabAfterGem, hGemNewEq,
                                        accountMapEquiv_sstoreAccountMap I.codeOwner
                                          (grabGemVSlot I) (grabGemNew σ_solm I) hAfterIlk]
                                    have hSinOldEq :
                                        solcSlotWord (grabAfterGem σ_evm I) I
                                          (grabSinSlot I) =
                                          solcSlotWord (grabAfterGem σ_solm I) I
                                            (grabSinSlot I) :=
                                      accountMapEquiv_storage_findD hAfterGem I.codeOwner
                                        (grabSinSlot I) ⟨0⟩
                                    have hDtabEq : grabDtab σ_evm I = grabDtab σ_solm I := by
                                      simp [grabDtab, hRateEq]
                                    have hSinNewEq :
                                        grabSinNew σ_evm I = grabSinNew σ_solm I := by
                                      simp [grabSinNew, hSinOldEq, hDtabEq]
                                    have hAfterSin :
                                        accountMapEquiv (grabAfterSin σ_evm I)
                                          (grabAfterSin σ_solm I) := by
                                      simp [grabAfterSin, hSinNewEq,
                                        accountMapEquiv_sstoreAccountMap I.codeOwner
                                          (grabSinSlot I) (grabSinNew σ_solm I) hAfterGem]
                                    have hViceOldEq :
                                        solcSlotWord (grabAfterSin σ_evm I) I ⟨8⟩ =
                                          solcSlotWord (grabAfterSin σ_solm I) I ⟨8⟩ :=
                                      accountMapEquiv_storage_findD hAfterSin I.codeOwner
                                        ⟨8⟩ ⟨0⟩
                                    have hGemPosS :
                                        UInt256.sgt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                          UInt256.gt (grabGemNew σ_solm I)
                                            (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                              (grabGemVSlot I)) = ⟨0⟩ := by
                                      simpa [grabGemPosOk, grabGemNew, hGemOldEq] using hGemPos
                                    have hGemNegS :
                                        UInt256.slt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                          UInt256.lt (grabGemNew σ_solm I)
                                            (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                              (grabGemVSlot I)) = ⟨0⟩ := by
                                      simpa [grabGemNegOk, grabGemNew, hGemOldEq] using hGemNeg
                                    have hSinPosS :
                                        UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
                                          UInt256.gt (grabSinNew σ_solm I)
                                            (solcSlotWord (grabAfterGem σ_solm I) I
                                              (grabSinSlot I)) = ⟨0⟩ := by
                                      simpa [grabSinPosOk, grabSinNew, hSinOldEq, hDtabEq]
                                        using hSinPos
                                    have hSinNegS :
                                        UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
                                          UInt256.lt (grabSinNew σ_solm I)
                                            (solcSlotWord (grabAfterGem σ_solm I) I
                                              (grabSinSlot I)) = ⟨0⟩ := by
                                      simpa [grabSinNegOk, grabSinNew, hSinOldEq, hDtabEq]
                                        using hSinNeg
                                    have hVicePosS :
                                        UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
                                          UInt256.gt (grabViceNew σ_solm I)
                                            (solcSlotWord (grabAfterSin σ_solm I) I ⟨8⟩) =
                                            ⟨0⟩ := by
                                      simpa [grabVicePosOk, grabViceNew, hViceOldEq,
                                        hDtabEq] using hVicePos
                                    have hViceNegFailS :
                                        ¬ (UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
                                          UInt256.lt (grabViceNew σ_solm I)
                                            (solcSlotWord (grabAfterSin σ_solm I) I ⟨8⟩) =
                                            ⟨0⟩) := by
                                      intro h
                                      exact hViceNeg (by
                                        simpa [grabViceNegOk, grabViceNew, hViceOldEq,
                                          hDtabEq] using h)
                                    have hbody :=
                                      vatGrabSourceBodyPostDtabRevertFromBlock
                                        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                                        (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                        hwv hauthSolm hsz196 hInkGuardNeg hInkGuardPos
                                        hArtGuardNeg hArtGuardPos hIlkGuardNeg hIlkGuardPos
                                        dtab hDtabOk
                                        (by
                                          intro evm0' evm1' evm2' evm3'
                                          let evm4' := Solm.EVM.storageStore evm3'
                                            evm3'.executionEnv.codeOwner (grabGemSourceSlot I)
                                            (grabGemNew σ_solm I)
                                          let evm5' := Solm.EVM.storageStore evm4'
                                            evm4'.executionEnv.codeOwner (grabSinSourceSlot I)
                                            (grabSinNew σ_solm I)
                                          let localsGem :=
                                            grabStoreGemNew I (grabUrnInkNew σ_solm I)
                                              (grabUrnArtNew σ_solm I)
                                              (grabIlkArtNew σ_solm I) dtab
                                              (grabGemNew σ_solm I)
                                          let localsSin :=
                                            grabStoreSinNew I (grabUrnInkNew σ_solm I)
                                              (grabUrnArtNew σ_solm I)
                                              (grabIlkArtNew σ_solm I) dtab
                                              (grabGemNew σ_solm I) (grabSinNew σ_solm I)
                                          have hGemBlock :
                                              ExecBlock config
                                                { contract := contract,
                                                  locals := grabStoreDtab I
                                                    (grabUrnInkNew σ_solm I)
                                                    (grabUrnArtNew σ_solm I)
                                                    (grabIlkArtNew σ_solm I) dtab }
                                                evm3'
                                                (checkedSubSignedInto "gemNew"
                                                  (.storage (gemRef (.var "i") (.var "v")))
                                                  (.var "dink") ++
                                                [ .assign .storage
                                                  (gemRef (.var "i") (.var "v"))
                                                  (.var "gemNew") ])
                                                (.ok
                                                  { contract := contract, locals := localsGem }
                                                  evm4') := by
                                            exact execGrabGemUpdateOk
                                              (evm := evm3') (I := I)
                                              (grabStoreDtab I (grabUrnInkNew σ_solm I)
                                                (grabUrnArtNew σ_solm I)
                                                (grabIlkArtNew σ_solm I) dtab)
                                              (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                                (grabGemVSlot I))
                                              (grabGemNew σ_solm I) hsz196
                                              (grabStoreDtab_get_i I (grabUrnInkNew σ_solm I)
                                                (grabUrnArtNew σ_solm I)
                                                (grabIlkArtNew σ_solm I) dtab)
                                              (grabStoreDtab_get_v I (grabUrnInkNew σ_solm I)
                                                (grabUrnArtNew σ_solm I)
                                                (grabIlkArtNew σ_solm I) dtab)
                                              (grabStoreDtab_get_dink I
                                                (grabUrnInkNew σ_solm I)
                                                (grabUrnArtNew σ_solm I)
                                                (grabIlkArtNew σ_solm I) dtab)
                                              (grabStoreDtab_gem I (grabUrnInkNew σ_solm I)
                                                (grabUrnArtNew σ_solm I)
                                                (grabIlkArtNew σ_solm I) dtab)
                                              (by simpa [evm0', evm1', evm2', evm3'] using
                                                (grabSourceLoad_gem_staged (cA := cA)
                                                  (gh := gh) (bl := bl) (σ := σ_solm)
                                                  (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                                  hsz196))
                                              (by simp [grabGemNew])
                                              (grabDinkSubGuardNegCond hGemPosS)
                                              (grabDinkSubGuardPosCond hGemNegS)
                                          have hSinBlock :
                                              ExecBlock config
                                                { contract := contract, locals := localsGem }
                                                evm4'
                                                (checkedSubSignedInto "sinNew"
                                                  (.storage (sinRef (.var "w")))
                                                  (.var "dtab") ++
                                                [ .assign .storage (sinRef (.var "w"))
                                                  (.var "sinNew") ])
                                                (.ok
                                                  { contract := contract, locals := localsSin }
                                                  evm5') := by
                                            exact execGrabSinUpdateOk
                                              (evm := evm4') (I := I) (locals := localsGem)
                                              (solcSlotWord (grabAfterGem σ_solm I) I
                                                (grabSinSlot I))
                                              (grabSinNew σ_solm I) dtabWord dtab
                                              (by
                                                simpa [localsGem] using
                                                  grabStoreGemNew_get_w I
                                                    (grabUrnInkNew σ_solm I)
                                                    (grabUrnArtNew σ_solm I)
                                                    (grabIlkArtNew σ_solm I) dtab
                                                    (grabGemNew σ_solm I))
                                              (by
                                                simpa [localsGem] using
                                                  grabStoreGemNew_get_dtab I
                                                    (grabUrnInkNew σ_solm I)
                                                    (grabUrnArtNew σ_solm I)
                                                    (grabIlkArtNew σ_solm I) dtab
                                                    (grabGemNew σ_solm I))
                                              (by
                                                simpa [localsGem] using
                                                  grabStoreGemNew_sin I
                                                    (grabUrnInkNew σ_solm I)
                                                    (grabUrnArtNew σ_solm I)
                                                    (grabIlkArtNew σ_solm I) dtab
                                                    (grabGemNew σ_solm I))
                                              (by
                                                simpa [evm0', evm1', evm2', evm3', evm4']
                                                  using
                                                  (grabSourceLoad_sin_staged (cA := cA)
                                                    (gh := gh) (bl := bl) (σ := σ_solm)
                                                    (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                                    hsz196))
                                              hdtabMod (by simp [grabSinNew, dtabWord])
                                              (grabDtabSubGuardNegCond hdtabLo hdtabHi
                                                hdtabMod hSinPosS)
                                              (grabDtabSubGuardPosCond hdtabLo hdtabHi
                                                hdtabMod hSinNegS)
                                          have hViceRevert :
                                              ExecBlock config
                                                { contract := contract, locals := localsSin }
                                                evm5'
                                                (checkedSubSignedInto "viceNew"
                                                  (.storage viceRef) (.var "dtab"))
                                                .reverted := by
                                            exact execGrabViceSubCheckedRevertGuardPos
                                              (evm := evm5') localsSin
                                              (solcSlotWord (grabAfterSin σ_solm I) I ⟨8⟩)
                                              (grabViceNew σ_solm I) dtabWord dtab
                                              (by
                                                simpa [localsSin] using
                                                  grabStoreSinNew_get_dtab I
                                                    (grabUrnInkNew σ_solm I)
                                                    (grabUrnArtNew σ_solm I)
                                                    (grabIlkArtNew σ_solm I) dtab
                                                    (grabGemNew σ_solm I)
                                                    (grabSinNew σ_solm I))
                                              (by
                                                simpa [localsSin] using
                                                  grabStoreSinNew_vice I
                                                    (grabUrnInkNew σ_solm I)
                                                    (grabUrnArtNew σ_solm I)
                                                    (grabIlkArtNew σ_solm I) dtab
                                                    (grabGemNew σ_solm I)
                                                    (grabSinNew σ_solm I))
                                              (by
                                                simpa [evm0', evm1', evm2', evm3', evm4',
                                                  evm5'] using
                                                  (grabSourceLoad_vice_staged (cA := cA)
                                                    (gh := gh) (bl := bl) (σ := σ_solm)
                                                    (σ₀ := σ₀) (A := A) (I := I)
                                                    (g := g) hsz196))
                                              hdtabLo hdtabHi hdtabMod
                                              (by simp [grabViceNew, dtabWord])
                                              hVicePosS hViceNegFailS
                                          exact execGrabTailViceRevertFromBlock
                                            hGemBlock hSinBlock hViceRevert)
                                    obtain ⟨_, _, hGemRD⟩ := RD.vatGrabGemSubSuccess
                                      (h := by simpa [memUrn, memAuth] using hDtabRD)
                                      hmemUrn
                                      (by simpa [grabGemPosOk, grabGemNew] using hGemPos)
                                      (by simpa [grabGemNegOk, grabGemNew] using hGemNeg)
                                    obtain ⟨_, _, hSinRD⟩ := RD.vatGrabSinSubSuccess
                                      (h := by simpa [memGem, memUrn, memAuth, grabAfterGem]
                                        using hGemRD)
                                      hmemGem hperm
                                      (by simpa [grabSinPosOk, grabSinNew] using hSinPos)
                                      (by simpa [grabSinNegOk, grabSinNew] using hSinNeg)
                                    have hrev := RD.vatGrabViceSubRevert
                                      (h := by simpa [memSin, memGem, grabAfterSin]
                                        using hSinRD)
                                      hmemSin hperm
                                      (Or.inr ⟨by
                                        simpa [grabVicePosOk, grabViceNew] using hVicePos, by
                                        intro h
                                        exact hViceNeg (by
                                          simpa [grabViceNegOk, grabViceNew] using h)⟩)
                                    exact hrev.reEquivExecutionRevert hcode
                                      (vatDispatchGrab hsel) hdecode hbody
                                · have hGemOldEq :
                                      solcSlotWord (grabAfterIlkArt σ_evm I) I
                                        (grabGemVSlot I) =
                                        solcSlotWord (grabAfterIlkArt σ_solm I) I
                                          (grabGemVSlot I) :=
                                    accountMapEquiv_storage_findD hAfterIlk I.codeOwner
                                      (grabGemVSlot I) ⟨0⟩
                                  have hGemNewEq :
                                      grabGemNew σ_evm I = grabGemNew σ_solm I := by
                                    simp [grabGemNew, hGemOldEq]
                                  have hAfterGem :
                                      accountMapEquiv (grabAfterGem σ_evm I)
                                        (grabAfterGem σ_solm I) := by
                                    simp [grabAfterGem, hGemNewEq,
                                      accountMapEquiv_sstoreAccountMap I.codeOwner
                                        (grabGemVSlot I) (grabGemNew σ_solm I) hAfterIlk]
                                  have hSinOldEq :
                                      solcSlotWord (grabAfterGem σ_evm I) I
                                        (grabSinSlot I) =
                                        solcSlotWord (grabAfterGem σ_solm I) I
                                          (grabSinSlot I) :=
                                    accountMapEquiv_storage_findD hAfterGem I.codeOwner
                                      (grabSinSlot I) ⟨0⟩
                                  have hDtabEq : grabDtab σ_evm I = grabDtab σ_solm I := by
                                    simp [grabDtab, hRateEq]
                                  have hSinNewEq :
                                      grabSinNew σ_evm I = grabSinNew σ_solm I := by
                                    simp [grabSinNew, hSinOldEq, hDtabEq]
                                  have hAfterSin :
                                      accountMapEquiv (grabAfterSin σ_evm I)
                                        (grabAfterSin σ_solm I) := by
                                    simp [grabAfterSin, hSinNewEq,
                                      accountMapEquiv_sstoreAccountMap I.codeOwner
                                        (grabSinSlot I) (grabSinNew σ_solm I) hAfterGem]
                                  have hViceOldEq :
                                      solcSlotWord (grabAfterSin σ_evm I) I ⟨8⟩ =
                                        solcSlotWord (grabAfterSin σ_solm I) I ⟨8⟩ :=
                                    accountMapEquiv_storage_findD hAfterSin I.codeOwner
                                      ⟨8⟩ ⟨0⟩
                                  have hGemPosS :
                                      UInt256.sgt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                        UInt256.gt (grabGemNew σ_solm I)
                                          (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                            (grabGemVSlot I)) = ⟨0⟩ := by
                                    simpa [grabGemPosOk, grabGemNew, hGemOldEq] using hGemPos
                                  have hGemNegS :
                                      UInt256.slt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                        UInt256.lt (grabGemNew σ_solm I)
                                          (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                            (grabGemVSlot I)) = ⟨0⟩ := by
                                    simpa [grabGemNegOk, grabGemNew, hGemOldEq] using hGemNeg
                                  have hSinPosS :
                                      UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
                                        UInt256.gt (grabSinNew σ_solm I)
                                          (solcSlotWord (grabAfterGem σ_solm I) I
                                            (grabSinSlot I)) = ⟨0⟩ := by
                                    simpa [grabSinPosOk, grabSinNew, hSinOldEq, hDtabEq]
                                      using hSinPos
                                  have hSinNegS :
                                      UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
                                        UInt256.lt (grabSinNew σ_solm I)
                                          (solcSlotWord (grabAfterGem σ_solm I) I
                                            (grabSinSlot I)) = ⟨0⟩ := by
                                    simpa [grabSinNegOk, grabSinNew, hSinOldEq, hDtabEq]
                                      using hSinNeg
                                  have hVicePosFailS :
                                      ¬ (UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
                                        UInt256.gt (grabViceNew σ_solm I)
                                          (solcSlotWord (grabAfterSin σ_solm I) I ⟨8⟩) =
                                          ⟨0⟩) := by
                                    intro h
                                    exact hVicePos (by
                                      simpa [grabVicePosOk, grabViceNew, hViceOldEq,
                                        hDtabEq] using h)
                                  have hbody :=
                                    vatGrabSourceBodyPostDtabRevertFromBlock
                                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                                      (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                      hwv hauthSolm hsz196 hInkGuardNeg hInkGuardPos
                                      hArtGuardNeg hArtGuardPos hIlkGuardNeg hIlkGuardPos
                                      dtab hDtabOk
                                      (by
                                        intro evm0' evm1' evm2' evm3'
                                        let evm4' := Solm.EVM.storageStore evm3'
                                          evm3'.executionEnv.codeOwner (grabGemSourceSlot I)
                                          (grabGemNew σ_solm I)
                                        let evm5' := Solm.EVM.storageStore evm4'
                                          evm4'.executionEnv.codeOwner (grabSinSourceSlot I)
                                          (grabSinNew σ_solm I)
                                        let localsGem :=
                                          grabStoreGemNew I (grabUrnInkNew σ_solm I)
                                            (grabUrnArtNew σ_solm I)
                                            (grabIlkArtNew σ_solm I) dtab
                                            (grabGemNew σ_solm I)
                                        let localsSin :=
                                          grabStoreSinNew I (grabUrnInkNew σ_solm I)
                                            (grabUrnArtNew σ_solm I)
                                            (grabIlkArtNew σ_solm I) dtab
                                            (grabGemNew σ_solm I) (grabSinNew σ_solm I)
                                        have hGemBlock :
                                            ExecBlock config
                                              { contract := contract,
                                                locals := grabStoreDtab I
                                                  (grabUrnInkNew σ_solm I)
                                                  (grabUrnArtNew σ_solm I)
                                                  (grabIlkArtNew σ_solm I) dtab }
                                              evm3'
                                              (checkedSubSignedInto "gemNew"
                                                (.storage (gemRef (.var "i") (.var "v")))
                                                (.var "dink") ++
                                              [ .assign .storage
                                                (gemRef (.var "i") (.var "v"))
                                                (.var "gemNew") ])
                                              (.ok { contract := contract, locals := localsGem }
                                                evm4') := by
                                          exact execGrabGemUpdateOk
                                            (evm := evm3') (I := I)
                                            (grabStoreDtab I (grabUrnInkNew σ_solm I)
                                              (grabUrnArtNew σ_solm I)
                                              (grabIlkArtNew σ_solm I) dtab)
                                            (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                              (grabGemVSlot I))
                                            (grabGemNew σ_solm I) hsz196
                                            (grabStoreDtab_get_i I (grabUrnInkNew σ_solm I)
                                              (grabUrnArtNew σ_solm I)
                                              (grabIlkArtNew σ_solm I) dtab)
                                            (grabStoreDtab_get_v I (grabUrnInkNew σ_solm I)
                                              (grabUrnArtNew σ_solm I)
                                              (grabIlkArtNew σ_solm I) dtab)
                                            (grabStoreDtab_get_dink I (grabUrnInkNew σ_solm I)
                                              (grabUrnArtNew σ_solm I)
                                              (grabIlkArtNew σ_solm I) dtab)
                                            (grabStoreDtab_gem I (grabUrnInkNew σ_solm I)
                                              (grabUrnArtNew σ_solm I)
                                              (grabIlkArtNew σ_solm I) dtab)
                                            (by simpa [evm0', evm1', evm2', evm3'] using
                                              (grabSourceLoad_gem_staged (cA := cA) (gh := gh)
                                                (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                                                (A := A) (I := I) (g := g) hsz196))
                                            (by simp [grabGemNew])
                                            (grabDinkSubGuardNegCond hGemPosS)
                                            (grabDinkSubGuardPosCond hGemNegS)
                                        have hSinBlock :
                                            ExecBlock config
                                              { contract := contract, locals := localsGem }
                                              evm4'
                                              (checkedSubSignedInto "sinNew"
                                                (.storage (sinRef (.var "w"))) (.var "dtab") ++
                                              [ .assign .storage (sinRef (.var "w"))
                                                (.var "sinNew") ])
                                              (.ok { contract := contract, locals := localsSin }
                                                evm5') := by
                                          exact execGrabSinUpdateOk
                                            (evm := evm4') (I := I) (locals := localsGem)
                                            (solcSlotWord (grabAfterGem σ_solm I) I
                                              (grabSinSlot I))
                                            (grabSinNew σ_solm I) dtabWord dtab
                                            (by
                                              simpa [localsGem] using
                                                grabStoreGemNew_get_w I
                                                  (grabUrnInkNew σ_solm I)
                                                  (grabUrnArtNew σ_solm I)
                                                  (grabIlkArtNew σ_solm I) dtab
                                                  (grabGemNew σ_solm I))
                                            (by
                                              simpa [localsGem] using
                                                grabStoreGemNew_get_dtab I
                                                  (grabUrnInkNew σ_solm I)
                                                  (grabUrnArtNew σ_solm I)
                                                  (grabIlkArtNew σ_solm I) dtab
                                                  (grabGemNew σ_solm I))
                                            (by
                                              simpa [localsGem] using
                                                grabStoreGemNew_sin I
                                                  (grabUrnInkNew σ_solm I)
                                                  (grabUrnArtNew σ_solm I)
                                                  (grabIlkArtNew σ_solm I) dtab
                                                  (grabGemNew σ_solm I))
                                            (by
                                              simpa [evm0', evm1', evm2', evm3', evm4'] using
                                                (grabSourceLoad_sin_staged (cA := cA)
                                                  (gh := gh) (bl := bl) (σ := σ_solm)
                                                  (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                                  hsz196))
                                            hdtabMod (by simp [grabSinNew, dtabWord])
                                            (grabDtabSubGuardNegCond hdtabLo hdtabHi
                                              hdtabMod hSinPosS)
                                            (grabDtabSubGuardPosCond hdtabLo hdtabHi
                                              hdtabMod hSinNegS)
                                        have hViceRevert :
                                            ExecBlock config
                                              { contract := contract, locals := localsSin }
                                              evm5'
                                              (checkedSubSignedInto "viceNew"
                                                (.storage viceRef) (.var "dtab"))
                                              .reverted := by
                                          exact execGrabViceSubCheckedRevertGuardNeg
                                            (evm := evm5') localsSin
                                            (solcSlotWord (grabAfterSin σ_solm I) I ⟨8⟩)
                                            (grabViceNew σ_solm I) dtabWord dtab
                                            (by
                                              simpa [localsSin] using
                                                grabStoreSinNew_get_dtab I
                                                  (grabUrnInkNew σ_solm I)
                                                  (grabUrnArtNew σ_solm I)
                                                  (grabIlkArtNew σ_solm I) dtab
                                                  (grabGemNew σ_solm I)
                                                  (grabSinNew σ_solm I))
                                            (by
                                              simpa [localsSin] using
                                                grabStoreSinNew_vice I
                                                  (grabUrnInkNew σ_solm I)
                                                  (grabUrnArtNew σ_solm I)
                                                  (grabIlkArtNew σ_solm I) dtab
                                                  (grabGemNew σ_solm I)
                                                  (grabSinNew σ_solm I))
                                            (by
                                              simpa [evm0', evm1', evm2', evm3', evm4',
                                                evm5'] using
                                                (grabSourceLoad_vice_staged (cA := cA)
                                                  (gh := gh) (bl := bl) (σ := σ_solm)
                                                  (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                                  hsz196))
                                            hdtabLo hdtabHi hdtabMod
                                            (by simp [grabViceNew, dtabWord])
                                            hVicePosFailS
                                        exact execGrabTailViceRevertFromBlock
                                          hGemBlock hSinBlock hViceRevert)
                                  obtain ⟨_, _, hGemRD⟩ := RD.vatGrabGemSubSuccess
                                    (h := by simpa [memUrn, memAuth] using hDtabRD) hmemUrn
                                    (by simpa [grabGemPosOk, grabGemNew] using hGemPos)
                                    (by simpa [grabGemNegOk, grabGemNew] using hGemNeg)
                                  obtain ⟨_, _, hSinRD⟩ := RD.vatGrabSinSubSuccess
                                    (h := by simpa [memGem, memUrn, memAuth, grabAfterGem]
                                      using hGemRD)
                                    hmemGem hperm
                                    (by simpa [grabSinPosOk, grabSinNew] using hSinPos)
                                    (by simpa [grabSinNegOk, grabSinNew] using hSinNeg)
                                  have hrev := RD.vatGrabViceSubRevert
                                    (h := by simpa [memSin, memGem, grabAfterSin] using hSinRD)
                                    hmemSin hperm
                                    (Or.inl (by
                                      intro h
                                      exact hVicePos (by
                                        simpa [grabVicePosOk, grabViceNew] using h)))
                                  exact hrev.reEquivExecutionRevert hcode (vatDispatchGrab hsel)
                                    hdecode hbody
                              · have hGemOldEq :
                                    solcSlotWord (grabAfterIlkArt σ_evm I) I
                                      (grabGemVSlot I) =
                                      solcSlotWord (grabAfterIlkArt σ_solm I) I
                                        (grabGemVSlot I) :=
                                  accountMapEquiv_storage_findD hAfterIlk I.codeOwner
                                    (grabGemVSlot I) ⟨0⟩
                                have hGemNewEq :
                                    grabGemNew σ_evm I = grabGemNew σ_solm I := by
                                  simp [grabGemNew, hGemOldEq]
                                have hAfterGem :
                                    accountMapEquiv (grabAfterGem σ_evm I)
                                      (grabAfterGem σ_solm I) := by
                                  simp [grabAfterGem, hGemNewEq,
                                    accountMapEquiv_sstoreAccountMap I.codeOwner
                                      (grabGemVSlot I) (grabGemNew σ_solm I) hAfterIlk]
                                have hSinOldEq :
                                    solcSlotWord (grabAfterGem σ_evm I) I (grabSinSlot I) =
                                      solcSlotWord (grabAfterGem σ_solm I) I
                                        (grabSinSlot I) :=
                                  accountMapEquiv_storage_findD hAfterGem I.codeOwner
                                    (grabSinSlot I) ⟨0⟩
                                have hDtabEq : grabDtab σ_evm I = grabDtab σ_solm I := by
                                  simp [grabDtab, hRateEq]
                                have hGemPosS :
                                    UInt256.sgt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                      UInt256.gt (grabGemNew σ_solm I)
                                        (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                          (grabGemVSlot I)) = ⟨0⟩ := by
                                  simpa [grabGemPosOk, grabGemNew, hGemOldEq] using hGemPos
                                have hGemNegS :
                                    UInt256.slt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                      UInt256.lt (grabGemNew σ_solm I)
                                        (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                          (grabGemVSlot I)) = ⟨0⟩ := by
                                  simpa [grabGemNegOk, grabGemNew, hGemOldEq] using hGemNeg
                                have hSinPosS :
                                    UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
                                      UInt256.gt (grabSinNew σ_solm I)
                                        (solcSlotWord (grabAfterGem σ_solm I) I
                                          (grabSinSlot I)) = ⟨0⟩ := by
                                  simpa [grabSinPosOk, grabSinNew, hSinOldEq, hDtabEq]
                                    using hSinPos
                                have hSinNegFailS :
                                    ¬ (UInt256.slt dtabWord ⟨0⟩ = ⟨0⟩ ∨
                                      UInt256.lt (grabSinNew σ_solm I)
                                        (solcSlotWord (grabAfterGem σ_solm I) I
                                          (grabSinSlot I)) = ⟨0⟩) := by
                                  intro h
                                  exact hSinNeg (by
                                    simpa [grabSinNegOk, grabSinNew, hSinOldEq, hDtabEq]
                                      using h)
                                have hbody :=
                                  vatGrabSourceBodyPostDtabRevertFromBlock
                                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                                    (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                    hwv hauthSolm hsz196 hInkGuardNeg hInkGuardPos
                                    hArtGuardNeg hArtGuardPos hIlkGuardNeg hIlkGuardPos
                                    dtab hDtabOk
                                    (by
                                      intro evm0' evm1' evm2' evm3'
                                      let evm4' := Solm.EVM.storageStore evm3'
                                        evm3'.executionEnv.codeOwner (grabGemSourceSlot I)
                                        (grabGemNew σ_solm I)
                                      let localsGem :=
                                        grabStoreGemNew I (grabUrnInkNew σ_solm I)
                                          (grabUrnArtNew σ_solm I)
                                          (grabIlkArtNew σ_solm I) dtab
                                          (grabGemNew σ_solm I)
                                      have hGemBlock :
                                          ExecBlock config
                                            { contract := contract,
                                              locals := grabStoreDtab I
                                                (grabUrnInkNew σ_solm I)
                                                (grabUrnArtNew σ_solm I)
                                                (grabIlkArtNew σ_solm I) dtab }
                                            evm3'
                                            (checkedSubSignedInto "gemNew"
                                              (.storage (gemRef (.var "i") (.var "v")))
                                              (.var "dink") ++
                                            [ .assign .storage
                                              (gemRef (.var "i") (.var "v"))
                                              (.var "gemNew") ])
                                            (.ok { contract := contract, locals := localsGem }
                                              evm4') := by
                                        exact execGrabGemUpdateOk
                                          (evm := evm3') (I := I)
                                          (grabStoreDtab I (grabUrnInkNew σ_solm I)
                                            (grabUrnArtNew σ_solm I)
                                            (grabIlkArtNew σ_solm I) dtab)
                                          (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                            (grabGemVSlot I))
                                          (grabGemNew σ_solm I)
                                          hsz196
                                          (grabStoreDtab_get_i I (grabUrnInkNew σ_solm I)
                                            (grabUrnArtNew σ_solm I)
                                            (grabIlkArtNew σ_solm I) dtab)
                                          (grabStoreDtab_get_v I (grabUrnInkNew σ_solm I)
                                            (grabUrnArtNew σ_solm I)
                                            (grabIlkArtNew σ_solm I) dtab)
                                          (grabStoreDtab_get_dink I (grabUrnInkNew σ_solm I)
                                            (grabUrnArtNew σ_solm I)
                                            (grabIlkArtNew σ_solm I) dtab)
                                          (grabStoreDtab_gem I (grabUrnInkNew σ_solm I)
                                            (grabUrnArtNew σ_solm I)
                                            (grabIlkArtNew σ_solm I) dtab)
                                          (by simpa [evm0', evm1', evm2', evm3'] using
                                            (grabSourceLoad_gem_staged (cA := cA) (gh := gh)
                                              (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                                              (A := A) (I := I) (g := g) hsz196))
                                          (by simp [grabGemNew])
                                          (grabDinkSubGuardNegCond hGemPosS)
                                          (grabDinkSubGuardPosCond hGemNegS)
                                      have hSinRevert :
                                          ExecBlock config
                                            { contract := contract, locals := localsGem }
                                            evm4'
                                            (checkedSubSignedInto "sinNew"
                                              (.storage (sinRef (.var "w"))) (.var "dtab"))
                                            .reverted := by
                                        exact execGrabSinSubCheckedRevertGuardPos
                                          (evm := evm4') (I := I) localsGem
                                          (solcSlotWord (grabAfterGem σ_solm I) I
                                            (grabSinSlot I))
                                          (grabSinNew σ_solm I) dtabWord dtab
                                          (by
                                            simpa [localsGem] using
                                              grabStoreGemNew_get_w I (grabUrnInkNew σ_solm I)
                                                (grabUrnArtNew σ_solm I)
                                                (grabIlkArtNew σ_solm I) dtab
                                                (grabGemNew σ_solm I))
                                          (by
                                            simpa [localsGem] using
                                              grabStoreGemNew_get_dtab I
                                                (grabUrnInkNew σ_solm I)
                                                (grabUrnArtNew σ_solm I)
                                                (grabIlkArtNew σ_solm I) dtab
                                                (grabGemNew σ_solm I))
                                          (by
                                            simpa [localsGem] using
                                              grabStoreGemNew_sin I (grabUrnInkNew σ_solm I)
                                                (grabUrnArtNew σ_solm I)
                                                (grabIlkArtNew σ_solm I) dtab
                                                (grabGemNew σ_solm I))
                                          (by
                                            simpa [evm0', evm1', evm2', evm3', evm4'] using
                                              (grabSourceLoad_sin_staged (cA := cA) (gh := gh)
                                                (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                                                (A := A) (I := I) (g := g) hsz196))
                                          hdtabLo hdtabHi hdtabMod
                                          (by simp [grabSinNew, dtabWord])
                                          hSinPosS hSinNegFailS
                                      exact execGrabTailSinRevertFromBlock
                                        hGemBlock hSinRevert)
                                obtain ⟨_, _, hGemRD⟩ := RD.vatGrabGemSubSuccess
                                  (h := by simpa [memUrn, memAuth] using hDtabRD) hmemUrn
                                  (by simpa [grabGemPosOk, grabGemNew] using hGemPos)
                                  (by simpa [grabGemNegOk, grabGemNew] using hGemNeg)
                                have hrev := RD.vatGrabSinSubRevert
                                  (h := by simpa [memGem, memUrn, memAuth, grabAfterGem]
                                    using hGemRD)
                                  hmemGem hperm
                                  (Or.inr ⟨by
                                    simpa [grabSinPosOk, grabSinNew] using hSinPos, by
                                    intro h
                                    exact hSinNeg (by
                                      simpa [grabSinNegOk, grabSinNew] using h)⟩)
                                exact hrev.reEquivExecutionRevert hcode (vatDispatchGrab hsel)
                                  hdecode hbody
                            · have hGemOldEq :
                                  solcSlotWord (grabAfterIlkArt σ_evm I) I
                                    (grabGemVSlot I) =
                                    solcSlotWord (grabAfterIlkArt σ_solm I) I
                                      (grabGemVSlot I) :=
                                accountMapEquiv_storage_findD hAfterIlk I.codeOwner
                                  (grabGemVSlot I) ⟨0⟩
                              have hGemNewEq :
                                  grabGemNew σ_evm I = grabGemNew σ_solm I := by
                                simp [grabGemNew, hGemOldEq]
                              have hAfterGem :
                                  accountMapEquiv (grabAfterGem σ_evm I)
                                    (grabAfterGem σ_solm I) := by
                                simp [grabAfterGem, hGemNewEq,
                                  accountMapEquiv_sstoreAccountMap I.codeOwner
                                    (grabGemVSlot I) (grabGemNew σ_solm I) hAfterIlk]
                              have hSinOldEq :
                                  solcSlotWord (grabAfterGem σ_evm I) I (grabSinSlot I) =
                                    solcSlotWord (grabAfterGem σ_solm I) I (grabSinSlot I) :=
                                accountMapEquiv_storage_findD hAfterGem I.codeOwner
                                  (grabSinSlot I) ⟨0⟩
                              have hDtabEq : grabDtab σ_evm I = grabDtab σ_solm I := by
                                simp [grabDtab, hRateEq]
                              have hGemPosS :
                                  UInt256.sgt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                    UInt256.gt (grabGemNew σ_solm I)
                                      (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                        (grabGemVSlot I)) = ⟨0⟩ := by
                                simpa [grabGemPosOk, grabGemNew, hGemOldEq] using hGemPos
                              have hGemNegS :
                                  UInt256.slt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                    UInt256.lt (grabGemNew σ_solm I)
                                      (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                        (grabGemVSlot I)) = ⟨0⟩ := by
                                simpa [grabGemNegOk, grabGemNew, hGemOldEq] using hGemNeg
                              have hSinPosFailS :
                                  ¬ (UInt256.sgt dtabWord ⟨0⟩ = ⟨0⟩ ∨
                                    UInt256.gt (grabSinNew σ_solm I)
                                      (solcSlotWord (grabAfterGem σ_solm I) I
                                        (grabSinSlot I)) = ⟨0⟩) := by
                                intro h
                                exact hSinPos (by
                                  simpa [grabSinPosOk, grabSinNew, hSinOldEq, hDtabEq]
                                    using h)
                              have hbody :=
                                vatGrabSourceBodyPostDtabRevertFromBlock
                                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                                  (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                  hwv hauthSolm hsz196 hInkGuardNeg hInkGuardPos
                                  hArtGuardNeg hArtGuardPos hIlkGuardNeg hIlkGuardPos
                                  dtab hDtabOk
                                  (by
                                    intro evm0' evm1' evm2' evm3'
                                    let evm4' := Solm.EVM.storageStore evm3'
                                      evm3'.executionEnv.codeOwner (grabGemSourceSlot I)
                                      (grabGemNew σ_solm I)
                                    let localsGem :=
                                      grabStoreGemNew I (grabUrnInkNew σ_solm I)
                                        (grabUrnArtNew σ_solm I)
                                        (grabIlkArtNew σ_solm I) dtab
                                        (grabGemNew σ_solm I)
                                    have hGemBlock :
                                        ExecBlock config
                                          { contract := contract,
                                            locals := grabStoreDtab I
                                              (grabUrnInkNew σ_solm I)
                                              (grabUrnArtNew σ_solm I)
                                              (grabIlkArtNew σ_solm I) dtab }
                                          evm3'
                                          (checkedSubSignedInto "gemNew"
                                            (.storage (gemRef (.var "i") (.var "v")))
                                            (.var "dink") ++
                                          [ .assign .storage
                                            (gemRef (.var "i") (.var "v"))
                                            (.var "gemNew") ])
                                          (.ok { contract := contract, locals := localsGem }
                                            evm4') := by
                                      exact execGrabGemUpdateOk
                                        (evm := evm3') (I := I)
                                        (grabStoreDtab I (grabUrnInkNew σ_solm I)
                                          (grabUrnArtNew σ_solm I)
                                          (grabIlkArtNew σ_solm I) dtab)
                                        (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                          (grabGemVSlot I))
                                        (grabGemNew σ_solm I)
                                        hsz196
                                        (grabStoreDtab_get_i I (grabUrnInkNew σ_solm I)
                                          (grabUrnArtNew σ_solm I)
                                          (grabIlkArtNew σ_solm I) dtab)
                                        (grabStoreDtab_get_v I (grabUrnInkNew σ_solm I)
                                          (grabUrnArtNew σ_solm I)
                                          (grabIlkArtNew σ_solm I) dtab)
                                        (grabStoreDtab_get_dink I (grabUrnInkNew σ_solm I)
                                          (grabUrnArtNew σ_solm I)
                                          (grabIlkArtNew σ_solm I) dtab)
                                        (grabStoreDtab_gem I (grabUrnInkNew σ_solm I)
                                          (grabUrnArtNew σ_solm I)
                                          (grabIlkArtNew σ_solm I) dtab)
                                        (by simpa [evm0', evm1', evm2', evm3'] using
                                          (grabSourceLoad_gem_staged (cA := cA) (gh := gh)
                                            (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                                            (A := A) (I := I) (g := g) hsz196))
                                        (by simp [grabGemNew])
                                        (grabDinkSubGuardNegCond hGemPosS)
                                        (grabDinkSubGuardPosCond hGemNegS)
                                    have hSinRevert :
                                        ExecBlock config
                                          { contract := contract, locals := localsGem }
                                          evm4'
                                          (checkedSubSignedInto "sinNew"
                                            (.storage (sinRef (.var "w"))) (.var "dtab"))
                                          .reverted := by
                                      exact execGrabSinSubCheckedRevertGuardNeg
                                        (evm := evm4') (I := I) localsGem
                                        (solcSlotWord (grabAfterGem σ_solm I) I
                                          (grabSinSlot I))
                                        (grabSinNew σ_solm I) dtabWord dtab
                                        (by
                                          simpa [localsGem] using
                                            grabStoreGemNew_get_w I (grabUrnInkNew σ_solm I)
                                              (grabUrnArtNew σ_solm I)
                                              (grabIlkArtNew σ_solm I) dtab
                                              (grabGemNew σ_solm I))
                                        (by
                                          simpa [localsGem] using
                                            grabStoreGemNew_get_dtab I
                                              (grabUrnInkNew σ_solm I)
                                              (grabUrnArtNew σ_solm I)
                                              (grabIlkArtNew σ_solm I) dtab
                                              (grabGemNew σ_solm I))
                                        (by
                                          simpa [localsGem] using
                                            grabStoreGemNew_sin I (grabUrnInkNew σ_solm I)
                                              (grabUrnArtNew σ_solm I)
                                              (grabIlkArtNew σ_solm I) dtab
                                              (grabGemNew σ_solm I))
                                        (by simpa [evm0', evm1', evm2', evm3', evm4'] using
                                          (grabSourceLoad_sin_staged (cA := cA) (gh := gh)
                                            (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                                            (A := A) (I := I) (g := g) hsz196))
                                        hdtabLo hdtabHi hdtabMod
                                        (by simp [grabSinNew, dtabWord])
                                        hSinPosFailS
                                    exact execGrabTailSinRevertFromBlock hGemBlock hSinRevert)
                              obtain ⟨_, _, hGemRD⟩ := RD.vatGrabGemSubSuccess
                                (h := by simpa [memUrn, memAuth] using hDtabRD) hmemUrn
                                (by simpa [grabGemPosOk, grabGemNew] using hGemPos)
                                (by simpa [grabGemNegOk, grabGemNew] using hGemNeg)
                              have hrev := RD.vatGrabSinSubRevert
                                (h := by simpa [memGem, memUrn, memAuth, grabAfterGem]
                                  using hGemRD)
                                hmemGem hperm
                                (Or.inl (by
                                  intro h
                                  exact hSinPos (by
                                    simpa [grabSinPosOk, grabSinNew] using h)))
                              exact hrev.reEquivExecutionRevert hcode (vatDispatchGrab hsel)
                                hdecode hbody
                          · have hGemOldEq :
                                solcSlotWord (grabAfterIlkArt σ_evm I) I
                                  (grabGemVSlot I) =
                                  solcSlotWord (grabAfterIlkArt σ_solm I) I
                                    (grabGemVSlot I) :=
                              accountMapEquiv_storage_findD hAfterIlk I.codeOwner
                                (grabGemVSlot I) ⟨0⟩
                            have hGemPosS :
                                UInt256.sgt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                  UInt256.gt (grabGemNew σ_solm I)
                                    (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                      (grabGemVSlot I)) = ⟨0⟩ := by
                              simpa [grabGemPosOk, grabGemNew, hGemOldEq] using hGemPos
                            have hGemNegFailS :
                                ¬ (UInt256.slt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                  UInt256.lt (grabGemNew σ_solm I)
                                    (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                      (grabGemVSlot I)) = ⟨0⟩) := by
                              intro h
                              exact hGemNeg (by
                                simpa [grabGemNegOk, grabGemNew, hGemOldEq] using h)
                            have hbody :=
                              vatGrabSourceBodyPostDtabRevertFromBlock
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                                (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                hwv hauthSolm hsz196 hInkGuardNeg hInkGuardPos
                                hArtGuardNeg hArtGuardPos hIlkGuardNeg hIlkGuardPos
                                dtab hDtabOk
                                (by
                                  intro evm0' evm1' evm2' evm3'
                                  apply execGrabTailGemRevertFromBlock
                                  exact execGrabGemSubCheckedRevertGuardPos
                                    (evm := evm3') (I := I)
                                    (grabStoreDtab I (grabUrnInkNew σ_solm I)
                                      (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I)
                                      dtab)
                                    (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                      (grabGemVSlot I))
                                    (grabGemNew σ_solm I)
                                    hsz196
                                    (grabStoreDtab_get_i I (grabUrnInkNew σ_solm I)
                                      (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I)
                                      dtab)
                                    (grabStoreDtab_get_v I (grabUrnInkNew σ_solm I)
                                      (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I)
                                      dtab)
                                    (grabStoreDtab_get_dink I (grabUrnInkNew σ_solm I)
                                      (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I)
                                      dtab)
                                    (grabStoreDtab_gem I (grabUrnInkNew σ_solm I)
                                      (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I)
                                      dtab)
                                    (by simpa [evm0', evm1', evm2', evm3'] using
                                      (grabSourceLoad_gem_staged (cA := cA) (gh := gh)
                                        (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
                                        (I := I) (g := g) hsz196))
                                    (by simp [grabGemNew])
                                    hGemPosS hGemNegFailS)
                            have hrev := RD.vatGrabGemSubRevert
                              (h := by simpa [memUrn, memAuth] using hDtabRD) hmemUrn
                              (Or.inr ⟨by
                                simpa [grabGemPosOk, grabGemNew] using hGemPos, by
                                intro h
                                exact hGemNeg (by
                                  simpa [grabGemNegOk, grabGemNew] using h)⟩)
                            exact hrev.reEquivExecutionRevert hcode (vatDispatchGrab hsel)
                              hdecode hbody
                        · have hGemOldEq :
                              solcSlotWord (grabAfterIlkArt σ_evm I) I (grabGemVSlot I) =
                                solcSlotWord (grabAfterIlkArt σ_solm I) I
                                  (grabGemVSlot I) :=
                            accountMapEquiv_storage_findD hAfterIlk I.codeOwner
                              (grabGemVSlot I) ⟨0⟩
                          have hGemPosFailS :
                              ¬ (UInt256.sgt (grabDinkWord I) ⟨0⟩ = ⟨0⟩ ∨
                                UInt256.gt (grabGemNew σ_solm I)
                                  (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                    (grabGemVSlot I)) = ⟨0⟩) := by
                            intro h
                            exact hGemPos (by
                              simpa [grabGemPosOk, grabGemNew, hGemOldEq] using h)
                          have hbody :=
                            vatGrabSourceBodyPostDtabRevertFromBlock
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                              (σ₀ := σ₀) (A := A) (I := I) (g := g)
                              hwv hauthSolm hsz196 hInkGuardNeg hInkGuardPos
                              hArtGuardNeg hArtGuardPos hIlkGuardNeg hIlkGuardPos
                              dtab hDtabOk
                              (by
                                intro evm0' evm1' evm2' evm3'
                                apply execGrabTailGemRevertFromBlock
                                exact execGrabGemSubCheckedRevertGuardNeg
                                  (evm := evm3') (I := I)
                                  (grabStoreDtab I (grabUrnInkNew σ_solm I)
                                    (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I)
                                    dtab)
                                  (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                    (grabGemVSlot I))
                                  (grabGemNew σ_solm I)
                                  hsz196
                                  (grabStoreDtab_get_i I (grabUrnInkNew σ_solm I)
                                    (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I)
                                    dtab)
                                  (grabStoreDtab_get_v I (grabUrnInkNew σ_solm I)
                                    (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I)
                                    dtab)
                                  (grabStoreDtab_get_dink I (grabUrnInkNew σ_solm I)
                                    (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I)
                                    dtab)
                                  (grabStoreDtab_gem I (grabUrnInkNew σ_solm I)
                                    (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I)
                                    dtab)
                                  (by simpa [evm0', evm1', evm2', evm3'] using
                                    (grabSourceLoad_gem_staged (cA := cA) (gh := gh)
                                      (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
                                      (I := I) (g := g) hsz196))
                                  (by simp [grabGemNew])
                                  hGemPosFailS)
                          have hrev := RD.vatGrabGemSubRevert
                            (h := by simpa [memUrn, memAuth] using hDtabRD) hmemUrn
                            (Or.inl (by
                              intro h
                              exact hGemPos (by simpa [grabGemPosOk, grabGemNew] using h)))
                          exact hrev.reEquivExecutionRevert hcode (vatDispatchGrab hsel)
                            hdecode hbody
                      · rcases accountMapEquiv_grabAddGuards hAccounts hInkNeg hInkPos
                            hUrnArtNeg hUrnArtPos hIlkArtNeg hIlkArtPos with
                        ⟨hInkNegS, hInkPosS, hUrnArtNegS, hUrnArtPosS,
                          hIlkArtNegS, hIlkArtPosS, hAfterIlk⟩
                        have hRateEq :
                            solcSlotWord (grabAfterIlkArt σ_evm I) I (grabIlkRateSlot I) =
                              solcSlotWord (grabAfterIlkArt σ_solm I) I
                                (grabIlkRateSlot I) :=
                          accountMapEquiv_storage_findD hAfterIlk I.codeOwner
                            (grabIlkRateSlot I) ⟨0⟩
                        have hDtabMulFailE :
                            ¬ (grabDartWord I = ⟨0⟩ ∨
                              UInt256.eq
                                (UInt256.sdiv
                                  (UInt256.mul (grabDartWord I)
                                    (solcSlotWord (grabAfterIlkArt σ_evm I) I
                                      (grabIlkRateSlot I)))
                                  (grabDartWord I))
                                (solcSlotWord (grabAfterIlkArt σ_evm I) I
                                  (grabIlkRateSlot I)) ≠ ⟨0⟩) := by
                          intro h
                          exact hDtabMul (by simpa [grabDtabMulOk] using h)
                        have hDtabMulFailS :
                            ¬ (grabDartWord I = ⟨0⟩ ∨
                              UInt256.eq
                                (UInt256.sdiv
                                  (UInt256.mul (grabDartWord I)
                                    (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                      (grabIlkRateSlot I)))
                                  (grabDartWord I))
                                (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                  (grabIlkRateSlot I)) ≠ ⟨0⟩) := by
                          intro h
                          exact hDtabMul (by
                            simpa [grabDtabMulOk, hRateEq] using h)
                        by_cases hbadRange :
                            dtab < -((2 : Int) ^ 255) ∨ dtab ≥ (2 : Int) ^ 255
                        · have hInkGuardNeg :
                              0 ≤ grabDinkInt I ∨
                                (grabUrnInkNew σ_solm I).toNat ≤
                                  (vatSlotWord (grabUrnInkSlot I) σ_solm I).toNat := by
                            exact grabDinkAddGuardNegCond (by
                              simpa [grabInkNegOk, grabUrnInkNew, vatSlotWord] using hInkNegS)
                          have hInkGuardPos :
                              grabDinkInt I ≤ 0 ∨
                                (vatSlotWord (grabUrnInkSlot I) σ_solm I).toNat ≤
                                  (grabUrnInkNew σ_solm I).toNat := by
                            exact grabDinkAddGuardPosCond (by
                              simpa [grabInkPosOk, grabUrnInkNew, vatSlotWord] using hInkPosS)
                          have hArtGuardNeg :
                              0 ≤ grabDartInt I ∨
                                (grabUrnArtNew σ_solm I).toNat ≤
                                  (solcSlotWord (grabAfterUrnInk σ_solm I) I
                                    (grabUrnArtSlot I)).toNat := by
                            exact grabDartAddGuardNegCond (by
                              simpa [grabUrnArtNegOk, grabUrnArtNew] using hUrnArtNegS)
                          have hArtGuardPos :
                              grabDartInt I ≤ 0 ∨
                                (solcSlotWord (grabAfterUrnInk σ_solm I) I
                                  (grabUrnArtSlot I)).toNat ≤
                                  (grabUrnArtNew σ_solm I).toNat := by
                            exact grabDartAddGuardPosCond (by
                              simpa [grabUrnArtPosOk, grabUrnArtNew] using hUrnArtPosS)
                          have hIlkGuardNeg :
                              0 ≤ grabDartInt I ∨
                                (grabIlkArtNew σ_solm I).toNat ≤
                                  (solcSlotWord (grabAfterUrnArt σ_solm I) I
                                    (grabIlkArtSlot I)).toNat := by
                            exact grabDartAddGuardNegCond (by
                              simpa [grabIlkArtNegOk, grabIlkArtNew] using hIlkArtNegS)
                          have hIlkGuardPos :
                              grabDartInt I ≤ 0 ∨
                                (solcSlotWord (grabAfterUrnArt σ_solm I) I
                                  (grabIlkArtSlot I)).toNat ≤
                                  (grabIlkArtNew σ_solm I).toNat := by
                            exact grabDartAddGuardPosCond (by
                              simpa [grabIlkArtPosOk, grabIlkArtNew] using hIlkArtPosS)
                          have hbody :=
                            vatGrabSourceBodyDtabRevertFromBlock
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                              (σ₀ := σ₀) (A := A) (I := I) (g := g)
                              hwv hauthSolm hsz196 hInkGuardNeg hInkGuardPos hArtGuardNeg
                              hArtGuardPos hIlkGuardNeg hIlkGuardPos
                              (by
                                intro evm0 evm1 evm2 evm3
                                exact execGrabDtabMulCheckedRevertRange
                                  (evm := evm3) (I := I)
                                  (grabStoreIlkArtNew I (grabUrnInkNew σ_solm I)
                                    (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I))
                                  (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                    (grabIlkRateSlot I))
                                  dtab hsz196
                                  (grabStoreIlkArtNew_get_i I
                                    (grabUrnInkNew σ_solm I) (grabUrnArtNew σ_solm I)
                                    (grabIlkArtNew σ_solm I))
                                  (grabStoreIlkArtNew_get_dart I
                                    (grabUrnInkNew σ_solm I) (grabUrnArtNew σ_solm I)
                                    (grabIlkArtNew σ_solm I))
                                  (grabStoreIlkArtNew_ilks I
                                    (grabUrnInkNew σ_solm I) (grabUrnArtNew σ_solm I)
                                    (grabIlkArtNew σ_solm I))
                                  (by simpa [evm0, evm1, evm2, evm3] using
                                    (grabSourceLoad_ilkRate_staged (cA := cA) (gh := gh)
                                      (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
                                      (I := I) (g := g) hsz196))
                                  (by rfl) hbadRange)
                          have hmemAuth :
                              (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size =
                                96 :=
                            twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩
                              solcFreePtrMem_size
                          obtain ⟨_, _, hInk⟩ := RD.vatGrabUrnInkAddSuccess
                            (h := hafterAuth) hmemAuth
                            (by simpa [grabUrnInkNew] using hInkNeg)
                            (by simpa [grabUrnInkNew] using hInkPos)
                          obtain ⟨_, _, hArt⟩ := RD.vatGrabUrnArtAddSuccess
                            (h := by simpa [grabUrnInkNew] using hInk) hperm
                            (by simpa [grabUrnArtNegOk, grabUrnInkNew, grabAfterUrnInk,
                              grabUrnArtNew] using hUrnArtNeg)
                            (by simpa [grabUrnArtPosOk, grabUrnInkNew, grabAfterUrnInk,
                              grabUrnArtNew] using hUrnArtPos)
                          obtain ⟨_, _, hIlk⟩ := RD.vatGrabIlkArtAddSuccess
                            (h := by simpa [grabUrnInkNew, grabAfterUrnInk, grabUrnArtNew]
                              using hArt) hperm
                            (by simpa [grabIlkArtNegOk, grabUrnInkNew, grabAfterUrnInk,
                              grabUrnArtNew, grabAfterUrnArt, grabIlkArtNew]
                              using hIlkArtNeg)
                            (by simpa [grabIlkArtPosOk, grabUrnInkNew, grabAfterUrnInk,
                              grabUrnArtNew, grabAfterUrnArt, grabIlkArtNew]
                              using hIlkArtPos)
                          have hrev := RD.vatGrabDtabMulRevert
                            (h := by
                              simpa [grabUrnInkNew, grabAfterUrnInk, grabUrnArtNew,
                                grabAfterUrnArt, grabIlkArtNew] using hIlk) hperm
                            (Or.inr ⟨by
                              simpa [grabDtabMaxOk, grabUrnInkNew, grabAfterUrnInk,
                                grabUrnArtNew, grabAfterUrnArt, grabIlkArtNew,
                                grabAfterIlkArt] using hDtabMax, by
                              simpa [grabUrnInkNew, grabAfterUrnInk, grabUrnArtNew,
                                grabAfterUrnArt, grabIlkArtNew, grabAfterIlkArt]
                                using hDtabMulFailE⟩)
                          exact hrev.reEquivExecutionRevert hcode (vatDispatchGrab hsel)
                            hdecode hbody
                        · have hdtabLo : -((2 : Int) ^ 255) ≤ dtab :=
                            not_lt.mp (fun h => hbadRange (Or.inl h))
                          have hdtabHi : dtab < (2 : Int) ^ 255 :=
                            not_le.mp (fun h => hbadRange (Or.inr h))
                          have hprodHi :
                              Int.ofNat
                                (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                  (grabIlkRateSlot I)).toNat * grabDartInt I <
                                  (2 : Int) ^ 255 := by
                            change
                              Int.ofNat
                                (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                  (grabIlkRateSlot I)).toNat * grabDartInt I <
                                  (2 : Int) ^ 255 at hdtabHi
                            exact hdtabHi
                          have hdartWordNe : grabDartWord I ≠ ⟨0⟩ := by
                            intro hzero
                            exact hDtabMulFailS (Or.inl hzero)
                          by_cases hdartLow : (grabDartWord I).toNat < EVM.twoPow 255
                          · have hguardTrue :=
                              grab_dtab_word_guard_true_of_range_pos I
                                (rate := solcSlotWord (grabAfterIlkArt σ_solm I) I
                                  (grabIlkRateSlot I))
                                hdartLow hdartWordNe hprodHi
                            exact False.elim (hDtabMulFailS hguardTrue)
                          · have hprodLo :
                                -((2 : Int) ^ 255) ≤
                                  Int.ofNat
                                    (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                      (grabIlkRateSlot I)).toNat * grabDartInt I := by
                              change
                                -((2 : Int) ^ 255) ≤
                                  Int.ofNat
                                    (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                      (grabIlkRateSlot I)).toNat * grabDartInt I at hdtabLo
                              exact hdtabLo
                            have hrateNe :
                                solcSlotWord (grabAfterIlkArt σ_solm I) I
                                  (grabIlkRateSlot I) ≠ ⟨0⟩ := by
                              intro hzero
                              exact hDtabMulFailS
                                (grab_dtab_word_guard_true_of_rate_zero I hzero)
                            have hguardTrue :=
                              grab_dtab_word_guard_true_of_range_neg I
                                (rate := solcSlotWord (grabAfterIlkArt σ_solm I) I
                                  (grabIlkRateSlot I))
                                (not_lt.mp hdartLow) hrateNe hprodLo
                            exact False.elim (hDtabMulFailS hguardTrue)
                    · rcases accountMapEquiv_grabAddGuards hAccounts hInkNeg hInkPos
                          hUrnArtNeg hUrnArtPos hIlkArtNeg hIlkArtPos with
                        ⟨hInkNegS, hInkPosS, hUrnArtNegS, hUrnArtPosS,
                          hIlkArtNegS, hIlkArtPosS, hAfterIlk⟩
                      have hRateEq :
                          solcSlotWord (grabAfterIlkArt σ_evm I) I (grabIlkRateSlot I) =
                            solcSlotWord (grabAfterIlkArt σ_solm I) I
                              (grabIlkRateSlot I) :=
                        accountMapEquiv_storage_findD hAfterIlk I.codeOwner
                          (grabIlkRateSlot I) ⟨0⟩
                      have hDtabMaxFailS :
                          UInt256.slt
                            (solcSlotWord (grabAfterIlkArt σ_solm I) I
                              (grabIlkRateSlot I)) ⟨0⟩ ≠ ⟨0⟩ := by
                        intro hslt
                        exact hDtabMax (by
                          simpa [grabDtabMaxOk, hRateEq] using hslt)
                      have hInkGuardNeg :
                          0 ≤ grabDinkInt I ∨
                            (grabUrnInkNew σ_solm I).toNat ≤
                              (vatSlotWord (grabUrnInkSlot I) σ_solm I).toNat := by
                        exact grabDinkAddGuardNegCond (by
                          simpa [grabInkNegOk, grabUrnInkNew, vatSlotWord] using hInkNegS)
                      have hInkGuardPos :
                          grabDinkInt I ≤ 0 ∨
                            (vatSlotWord (grabUrnInkSlot I) σ_solm I).toNat ≤
                              (grabUrnInkNew σ_solm I).toNat := by
                        exact grabDinkAddGuardPosCond (by
                          simpa [grabInkPosOk, grabUrnInkNew, vatSlotWord] using hInkPosS)
                      have hArtGuardNeg :
                          0 ≤ grabDartInt I ∨
                            (grabUrnArtNew σ_solm I).toNat ≤
                              (solcSlotWord (grabAfterUrnInk σ_solm I) I
                                (grabUrnArtSlot I)).toNat := by
                        exact grabDartAddGuardNegCond (by
                          simpa [grabUrnArtNegOk, grabUrnArtNew] using hUrnArtNegS)
                      have hArtGuardPos :
                          grabDartInt I ≤ 0 ∨
                            (solcSlotWord (grabAfterUrnInk σ_solm I) I
                              (grabUrnArtSlot I)).toNat ≤
                              (grabUrnArtNew σ_solm I).toNat := by
                        exact grabDartAddGuardPosCond (by
                          simpa [grabUrnArtPosOk, grabUrnArtNew] using hUrnArtPosS)
                      have hIlkGuardNeg :
                          0 ≤ grabDartInt I ∨
                            (grabIlkArtNew σ_solm I).toNat ≤
                              (solcSlotWord (grabAfterUrnArt σ_solm I) I
                                (grabIlkArtSlot I)).toNat := by
                        exact grabDartAddGuardNegCond (by
                          simpa [grabIlkArtNegOk, grabIlkArtNew] using hIlkArtNegS)
                      have hIlkGuardPos :
                          grabDartInt I ≤ 0 ∨
                            (solcSlotWord (grabAfterUrnArt σ_solm I) I
                              (grabIlkArtSlot I)).toNat ≤
                              (grabIlkArtNew σ_solm I).toNat := by
                        exact grabDartAddGuardPosCond (by
                          simpa [grabIlkArtPosOk, grabIlkArtNew] using hIlkArtPosS)
                      by_cases hbadRange :
                          dtab < -((2 : Int) ^ 255) ∨ dtab ≥ (2 : Int) ^ 255
                      · have hbody :=
                          vatGrabSourceBodyDtabRevertFromBlock
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                            (σ₀ := σ₀) (A := A) (I := I) (g := g)
                            hwv hauthSolm hsz196 hInkGuardNeg hInkGuardPos hArtGuardNeg
                            hArtGuardPos hIlkGuardNeg hIlkGuardPos
                            (by
                              intro evm0 evm1 evm2 evm3
                              exact execGrabDtabMulCheckedRevertRange
                                (evm := evm3) (I := I)
                                (grabStoreIlkArtNew I (grabUrnInkNew σ_solm I)
                                  (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I))
                                (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                  (grabIlkRateSlot I))
                                dtab hsz196
                                (grabStoreIlkArtNew_get_i I
                                  (grabUrnInkNew σ_solm I) (grabUrnArtNew σ_solm I)
                                  (grabIlkArtNew σ_solm I))
                                (grabStoreIlkArtNew_get_dart I
                                  (grabUrnInkNew σ_solm I) (grabUrnArtNew σ_solm I)
                                  (grabIlkArtNew σ_solm I))
                                (grabStoreIlkArtNew_ilks I
                                  (grabUrnInkNew σ_solm I) (grabUrnArtNew σ_solm I)
                                  (grabIlkArtNew σ_solm I))
                                (by simpa [evm0, evm1, evm2, evm3] using
                                  (grabSourceLoad_ilkRate_staged (cA := cA) (gh := gh)
                                    (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
                                    (I := I) (g := g) hsz196))
                                (by rfl) hbadRange)
                        have hmemAuth :
                            (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size =
                              96 :=
                          twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩
                            solcFreePtrMem_size
                        obtain ⟨_, _, hInk⟩ := RD.vatGrabUrnInkAddSuccess
                          (h := hafterAuth) hmemAuth
                          (by simpa [grabUrnInkNew] using hInkNeg)
                          (by simpa [grabUrnInkNew] using hInkPos)
                        obtain ⟨_, _, hArt⟩ := RD.vatGrabUrnArtAddSuccess
                          (h := by simpa [grabUrnInkNew] using hInk) hperm
                          (by simpa [grabUrnArtNegOk, grabUrnInkNew, grabAfterUrnInk,
                            grabUrnArtNew] using hUrnArtNeg)
                          (by simpa [grabUrnArtPosOk, grabUrnInkNew, grabAfterUrnInk,
                            grabUrnArtNew] using hUrnArtPos)
                        obtain ⟨_, _, hIlk⟩ := RD.vatGrabIlkArtAddSuccess
                          (h := by simpa [grabUrnInkNew, grabAfterUrnInk, grabUrnArtNew]
                            using hArt) hperm
                          (by simpa [grabIlkArtNegOk, grabUrnInkNew, grabAfterUrnInk,
                            grabUrnArtNew, grabAfterUrnArt, grabIlkArtNew]
                            using hIlkArtNeg)
                          (by simpa [grabIlkArtPosOk, grabUrnInkNew, grabAfterUrnInk,
                            grabUrnArtNew, grabAfterUrnArt, grabIlkArtNew]
                            using hIlkArtPos)
                        have hrev := RD.vatGrabDtabMulRevert
                          (h := by
                            simpa [grabUrnInkNew, grabAfterUrnInk, grabUrnArtNew,
                              grabAfterUrnArt, grabIlkArtNew] using hIlk) hperm
                          (Or.inl (by
                            simpa [grabDtabMaxOk, grabUrnInkNew, grabAfterUrnInk,
                              grabUrnArtNew, grabAfterUrnArt, grabIlkArtNew,
                              grabAfterIlkArt] using hDtabMax))
                        exact hrev.reEquivExecutionRevert hcode (vatDispatchGrab hsel)
                          hdecode hbody
                      · have hdtabLo : -((2 : Int) ^ 255) ≤ dtab :=
                          not_lt.mp (fun h => hbadRange (Or.inl h))
                        have hdtabHi : dtab < (2 : Int) ^ 255 :=
                          not_le.mp (fun h => hbadRange (Or.inr h))
                        have hbody :=
                          vatGrabSourceBodyDtabRevertFromBlock
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                            (σ₀ := σ₀) (A := A) (I := I) (g := g)
                            hwv hauthSolm hsz196 hInkGuardNeg hInkGuardPos hArtGuardNeg
                            hArtGuardPos hIlkGuardNeg hIlkGuardPos
                            (by
                              intro evm0 evm1 evm2 evm3
                              exact execGrabDtabMulCheckedRevertMaxSlt
                                (evm := evm3) (I := I)
                                (grabStoreIlkArtNew I (grabUrnInkNew σ_solm I)
                                  (grabUrnArtNew σ_solm I) (grabIlkArtNew σ_solm I))
                                (solcSlotWord (grabAfterIlkArt σ_solm I) I
                                  (grabIlkRateSlot I))
                                dtab hsz196
                                (grabStoreIlkArtNew_get_i I
                                  (grabUrnInkNew σ_solm I) (grabUrnArtNew σ_solm I)
                                  (grabIlkArtNew σ_solm I))
                                (grabStoreIlkArtNew_get_dart I
                                  (grabUrnInkNew σ_solm I) (grabUrnArtNew σ_solm I)
                                  (grabIlkArtNew σ_solm I))
                                (grabStoreIlkArtNew_ilks I
                                  (grabUrnInkNew σ_solm I) (grabUrnArtNew σ_solm I)
                                  (grabIlkArtNew σ_solm I))
                                (by simpa [evm0, evm1, evm2, evm3] using
                                  (grabSourceLoad_ilkRate_staged (cA := cA) (gh := gh)
                                    (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
                                    (I := I) (g := g) hsz196))
                                (by rfl) hdtabLo hdtabHi hDtabMaxFailS)
                        have hmemAuth :
                            (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size =
                              96 :=
                          twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩
                            solcFreePtrMem_size
                        obtain ⟨_, _, hInk⟩ := RD.vatGrabUrnInkAddSuccess
                          (h := hafterAuth) hmemAuth
                          (by simpa [grabUrnInkNew] using hInkNeg)
                          (by simpa [grabUrnInkNew] using hInkPos)
                        obtain ⟨_, _, hArt⟩ := RD.vatGrabUrnArtAddSuccess
                          (h := by simpa [grabUrnInkNew] using hInk) hperm
                          (by simpa [grabUrnArtNegOk, grabUrnInkNew, grabAfterUrnInk,
                            grabUrnArtNew] using hUrnArtNeg)
                          (by simpa [grabUrnArtPosOk, grabUrnInkNew, grabAfterUrnInk,
                            grabUrnArtNew] using hUrnArtPos)
                        obtain ⟨_, _, hIlk⟩ := RD.vatGrabIlkArtAddSuccess
                          (h := by simpa [grabUrnInkNew, grabAfterUrnInk, grabUrnArtNew]
                            using hArt) hperm
                          (by simpa [grabIlkArtNegOk, grabUrnInkNew, grabAfterUrnInk,
                            grabUrnArtNew, grabAfterUrnArt, grabIlkArtNew]
                            using hIlkArtNeg)
                          (by simpa [grabIlkArtPosOk, grabUrnInkNew, grabAfterUrnInk,
                            grabUrnArtNew, grabAfterUrnArt, grabIlkArtNew]
                            using hIlkArtPos)
                        have hrev := RD.vatGrabDtabMulRevert
                          (h := by
                            simpa [grabUrnInkNew, grabAfterUrnInk, grabUrnArtNew,
                              grabAfterUrnArt, grabIlkArtNew] using hIlk) hperm
                          (Or.inl (by
                            simpa [grabDtabMaxOk, grabUrnInkNew, grabAfterUrnInk,
                              grabUrnArtNew, grabAfterUrnArt, grabIlkArtNew,
                              grabAfterIlkArt] using hDtabMax))
                        exact hrev.reEquivExecutionRevert hcode (vatDispatchGrab hsel)
                          hdecode hbody
                  · have hInkOldEq :
                        solcSlotWord σ_evm I (grabUrnInkSlot I) =
                          solcSlotWord σ_solm I (grabUrnInkSlot I) :=
                        accountMapEquiv_storage_findD hAccounts I.codeOwner
                          (grabUrnInkSlot I) ⟨0⟩
                    have hInkNewEq : grabUrnInkNew σ_evm I = grabUrnInkNew σ_solm I := by
                      simp [grabUrnInkNew, hInkOldEq]
                    have hAfterInk :
                        accountMapEquiv (grabAfterUrnInk σ_evm I)
                          (grabAfterUrnInk σ_solm I) := by
                      simp [grabAfterUrnInk, hInkNewEq,
                        accountMapEquiv_sstoreAccountMap I.codeOwner (grabUrnInkSlot I)
                          (grabUrnInkNew σ_solm I) hAccounts]
                    have hArtOldEq :
                        solcSlotWord (grabAfterUrnInk σ_evm I) I (grabUrnArtSlot I) =
                          solcSlotWord (grabAfterUrnInk σ_solm I) I (grabUrnArtSlot I) :=
                        accountMapEquiv_storage_findD hAfterInk I.codeOwner
                          (grabUrnArtSlot I) ⟨0⟩
                    have hArtNewEq : grabUrnArtNew σ_evm I = grabUrnArtNew σ_solm I := by
                      simp [grabUrnArtNew, hArtOldEq]
                    have hAfterArt :
                        accountMapEquiv (grabAfterUrnArt σ_evm I)
                          (grabAfterUrnArt σ_solm I) := by
                      simp [grabAfterUrnArt, hArtNewEq,
                        accountMapEquiv_sstoreAccountMap I.codeOwner (grabUrnArtSlot I)
                          (grabUrnArtNew σ_solm I) hAfterInk]
                    have hIlkOldEq :
                        solcSlotWord (grabAfterUrnArt σ_evm I) I (grabIlkArtSlot I) =
                          solcSlotWord (grabAfterUrnArt σ_solm I) I (grabIlkArtSlot I) :=
                        accountMapEquiv_storage_findD hAfterArt I.codeOwner
                          (grabIlkArtSlot I) ⟨0⟩
                    have hIlkNewEq : grabIlkArtNew σ_evm I = grabIlkArtNew σ_solm I := by
                      simp [grabIlkArtNew, hIlkOldEq]
                    have hInkNegSolm : grabInkNegOk σ_solm I := by
                      simpa [grabInkNegOk, hInkOldEq, hInkNewEq] using hInkNeg
                    have hInkPosSolm : grabInkPosOk σ_solm I := by
                      simpa [grabInkPosOk, hInkOldEq, hInkNewEq] using hInkPos
                    have hUrnArtNegSolm : grabUrnArtNegOk σ_solm I := by
                      simpa [grabUrnArtNegOk, hArtOldEq, hArtNewEq] using hUrnArtNeg
                    have hUrnArtPosSolm : grabUrnArtPosOk σ_solm I := by
                      simpa [grabUrnArtPosOk, hArtOldEq, hArtNewEq] using hUrnArtPos
                    have hIlkArtNegSolm : grabIlkArtNegOk σ_solm I := by
                      simpa [grabIlkArtNegOk, hIlkOldEq, hIlkNewEq] using hIlkArtNeg
                    have hIlkArtPosFailSolm : ¬ grabIlkArtPosOk σ_solm I := by
                      intro hIlkArtPosSolm
                      exact hIlkArtPos (by
                        simpa [grabIlkArtPosOk, hIlkOldEq, hIlkNewEq] using
                          hIlkArtPosSolm)
                    have hInkGuardNeg :
                        0 ≤ grabDinkInt I ∨
                          (grabUrnInkNew σ_solm I).toNat ≤
                            (vatSlotWord (grabUrnInkSlot I) σ_solm I).toNat := by
                      exact grabDinkAddGuardNegCond (by
                        simpa [grabInkNegOk, grabUrnInkNew, vatSlotWord] using hInkNegSolm)
                    have hInkGuardPos :
                        grabDinkInt I ≤ 0 ∨
                          (vatSlotWord (grabUrnInkSlot I) σ_solm I).toNat ≤
                            (grabUrnInkNew σ_solm I).toNat := by
                      exact grabDinkAddGuardPosCond (by
                        simpa [grabInkPosOk, grabUrnInkNew, vatSlotWord] using hInkPosSolm)
                    have hArtGuardNeg :
                        0 ≤ grabDartInt I ∨
                          (grabUrnArtNew σ_solm I).toNat ≤
                            (solcSlotWord (grabAfterUrnInk σ_solm I) I
                              (grabUrnArtSlot I)).toNat := by
                      exact grabDartAddGuardNegCond (by
                        simpa [grabUrnArtNegOk, grabUrnArtNew] using hUrnArtNegSolm)
                    have hArtGuardPos :
                        grabDartInt I ≤ 0 ∨
                          (solcSlotWord (grabAfterUrnInk σ_solm I) I
                            (grabUrnArtSlot I)).toNat ≤
                            (grabUrnArtNew σ_solm I).toNat := by
                      exact grabDartAddGuardPosCond (by
                        simpa [grabUrnArtPosOk, grabUrnArtNew] using hUrnArtPosSolm)
                    have hIlkGuardNeg :
                        0 ≤ grabDartInt I ∨
                          (grabIlkArtNew σ_solm I).toNat ≤
                            (solcSlotWord (grabAfterUrnArt σ_solm I) I
                              (grabIlkArtSlot I)).toNat := by
                      exact grabDartAddGuardNegCond (by
                        simpa [grabIlkArtNegOk, grabIlkArtNew] using hIlkArtNegSolm)
                    have hIlkGuardPos :
                        0 < grabDartInt I ∧
                          (grabIlkArtNew σ_solm I).toNat <
                            (solcSlotWord (grabAfterUrnArt σ_solm I) I
                              (grabIlkArtSlot I)).toNat := by
                      exact signedAddGuardPosFalseCond_of_word
                        (grabDartInt_lo I) (grabDartInt_hi I) (grabDartInt_mod_word I)
                        (by
                          intro h
                          exact hIlkArtPosFailSolm (by
                            simpa [grabIlkArtPosOk, grabIlkArtNew] using h))
                    have hbody :=
                      vatGrabSourceBodyIlkArtRevertGuardPos
                        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                        (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        hwv hauthSolm hsz196 hInkGuardNeg hInkGuardPos hArtGuardNeg
                        hArtGuardPos hIlkGuardNeg hIlkGuardPos
                    have hmemAuth :
                        (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
                      twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
                    obtain ⟨_, _, hInk⟩ := RD.vatGrabUrnInkAddSuccess
                      (h := hafterAuth) hmemAuth
                      (by simpa [grabUrnInkNew] using hInkNeg)
                      (by simpa [grabUrnInkNew] using hInkPos)
                    obtain ⟨_, _, hArt⟩ := RD.vatGrabUrnArtAddSuccess
                      (h := by simpa [grabUrnInkNew] using hInk) hperm
                      (by simpa [grabUrnArtNegOk, grabUrnInkNew, grabAfterUrnInk,
                        grabUrnArtNew] using hUrnArtNeg)
                      (by simpa [grabUrnArtPosOk, grabUrnInkNew, grabAfterUrnInk,
                        grabUrnArtNew] using hUrnArtPos)
                    have hrev := RD.vatGrabIlkArtAddRevert
                      (h := by simpa [grabUrnInkNew, grabAfterUrnInk, grabUrnArtNew]
                        using hArt) hperm
                      (Or.inr ⟨
                        (by simpa [grabIlkArtNegOk, grabUrnInkNew, grabAfterUrnInk,
                          grabUrnArtNew, grabAfterUrnArt, grabIlkArtNew]
                          using hIlkArtNeg),
                        (by simpa [grabIlkArtPosOk, grabUrnInkNew, grabAfterUrnInk,
                          grabUrnArtNew, grabAfterUrnArt, grabIlkArtNew]
                          using hIlkArtPos)⟩)
                    exact hrev.reEquivExecutionRevert hcode (vatDispatchGrab hsel) hdecode
                      hbody
                · have hInkOldEq :
                      solcSlotWord σ_evm I (grabUrnInkSlot I) =
                        solcSlotWord σ_solm I (grabUrnInkSlot I) :=
                      accountMapEquiv_storage_findD hAccounts I.codeOwner
                        (grabUrnInkSlot I) ⟨0⟩
                  have hInkNewEq : grabUrnInkNew σ_evm I = grabUrnInkNew σ_solm I := by
                    simp [grabUrnInkNew, hInkOldEq]
                  have hAfterInk :
                      accountMapEquiv (grabAfterUrnInk σ_evm I)
                        (grabAfterUrnInk σ_solm I) := by
                    simp [grabAfterUrnInk, hInkNewEq,
                      accountMapEquiv_sstoreAccountMap I.codeOwner (grabUrnInkSlot I)
                        (grabUrnInkNew σ_solm I) hAccounts]
                  have hArtOldEq :
                      solcSlotWord (grabAfterUrnInk σ_evm I) I (grabUrnArtSlot I) =
                        solcSlotWord (grabAfterUrnInk σ_solm I) I (grabUrnArtSlot I) :=
                      accountMapEquiv_storage_findD hAfterInk I.codeOwner
                        (grabUrnArtSlot I) ⟨0⟩
                  have hArtNewEq : grabUrnArtNew σ_evm I = grabUrnArtNew σ_solm I := by
                    simp [grabUrnArtNew, hArtOldEq]
                  have hAfterArt :
                      accountMapEquiv (grabAfterUrnArt σ_evm I)
                        (grabAfterUrnArt σ_solm I) := by
                    simp [grabAfterUrnArt, hArtNewEq,
                      accountMapEquiv_sstoreAccountMap I.codeOwner (grabUrnArtSlot I)
                        (grabUrnArtNew σ_solm I) hAfterInk]
                  have hIlkOldEq :
                      solcSlotWord (grabAfterUrnArt σ_evm I) I (grabIlkArtSlot I) =
                        solcSlotWord (grabAfterUrnArt σ_solm I) I (grabIlkArtSlot I) :=
                      accountMapEquiv_storage_findD hAfterArt I.codeOwner
                        (grabIlkArtSlot I) ⟨0⟩
                  have hIlkNewEq : grabIlkArtNew σ_evm I = grabIlkArtNew σ_solm I := by
                    simp [grabIlkArtNew, hIlkOldEq]
                  have hInkNegSolm : grabInkNegOk σ_solm I := by
                    simpa [grabInkNegOk, hInkOldEq, hInkNewEq] using hInkNeg
                  have hInkPosSolm : grabInkPosOk σ_solm I := by
                    simpa [grabInkPosOk, hInkOldEq, hInkNewEq] using hInkPos
                  have hUrnArtNegSolm : grabUrnArtNegOk σ_solm I := by
                    simpa [grabUrnArtNegOk, hArtOldEq, hArtNewEq] using hUrnArtNeg
                  have hUrnArtPosSolm : grabUrnArtPosOk σ_solm I := by
                    simpa [grabUrnArtPosOk, hArtOldEq, hArtNewEq] using hUrnArtPos
                  have hIlkArtNegFailSolm : ¬ grabIlkArtNegOk σ_solm I := by
                    intro hIlkArtNegSolm
                    exact hIlkArtNeg (by
                      simpa [grabIlkArtNegOk, hIlkOldEq, hIlkNewEq] using
                        hIlkArtNegSolm)
                  have hInkGuardNeg :
                      0 ≤ grabDinkInt I ∨
                        (grabUrnInkNew σ_solm I).toNat ≤
                          (vatSlotWord (grabUrnInkSlot I) σ_solm I).toNat := by
                    exact grabDinkAddGuardNegCond (by
                      simpa [grabInkNegOk, grabUrnInkNew, vatSlotWord] using hInkNegSolm)
                  have hInkGuardPos :
                      grabDinkInt I ≤ 0 ∨
                        (vatSlotWord (grabUrnInkSlot I) σ_solm I).toNat ≤
                          (grabUrnInkNew σ_solm I).toNat := by
                    exact grabDinkAddGuardPosCond (by
                      simpa [grabInkPosOk, grabUrnInkNew, vatSlotWord] using hInkPosSolm)
                  have hArtGuardNeg :
                      0 ≤ grabDartInt I ∨
                        (grabUrnArtNew σ_solm I).toNat ≤
                          (solcSlotWord (grabAfterUrnInk σ_solm I) I
                            (grabUrnArtSlot I)).toNat := by
                    exact grabDartAddGuardNegCond (by
                      simpa [grabUrnArtNegOk, grabUrnArtNew] using hUrnArtNegSolm)
                  have hArtGuardPos :
                      grabDartInt I ≤ 0 ∨
                        (solcSlotWord (grabAfterUrnInk σ_solm I) I
                          (grabUrnArtSlot I)).toNat ≤
                          (grabUrnArtNew σ_solm I).toNat := by
                    exact grabDartAddGuardPosCond (by
                      simpa [grabUrnArtPosOk, grabUrnArtNew] using hUrnArtPosSolm)
                  have hIlkGuardNeg :
                      grabDartInt I < 0 ∧
                        (solcSlotWord (grabAfterUrnArt σ_solm I) I
                          (grabIlkArtSlot I)).toNat <
                          (grabIlkArtNew σ_solm I).toNat := by
                    exact signedAddGuardNegFalseCond_of_word
                      (grabDartInt_lo I) (grabDartInt_hi I) (grabDartInt_mod_word I)
                      (by
                        intro h
                        exact hIlkArtNegFailSolm (by
                          simpa [grabIlkArtNegOk, grabIlkArtNew] using h))
                  have hbody :=
                    vatGrabSourceBodyIlkArtRevertGuardNeg
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                      (σ₀ := σ₀) (A := A) (I := I) (g := g)
                      hwv hauthSolm hsz196 hInkGuardNeg hInkGuardPos hArtGuardNeg
                      hArtGuardPos hIlkGuardNeg
                  have hmemAuth :
                      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
                    twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
                  obtain ⟨_, _, hInk⟩ := RD.vatGrabUrnInkAddSuccess
                    (h := hafterAuth) hmemAuth
                    (by simpa [grabUrnInkNew] using hInkNeg)
                    (by simpa [grabUrnInkNew] using hInkPos)
                  obtain ⟨_, _, hArt⟩ := RD.vatGrabUrnArtAddSuccess
                    (h := by simpa [grabUrnInkNew] using hInk) hperm
                    (by simpa [grabUrnArtNegOk, grabUrnInkNew, grabAfterUrnInk,
                      grabUrnArtNew] using hUrnArtNeg)
                    (by simpa [grabUrnArtPosOk, grabUrnInkNew, grabAfterUrnInk,
                      grabUrnArtNew] using hUrnArtPos)
                  have hrev := RD.vatGrabIlkArtAddRevert
                    (h := by simpa [grabUrnInkNew, grabAfterUrnInk, grabUrnArtNew]
                      using hArt) hperm
                    (Or.inl (by simpa [grabIlkArtNegOk, grabUrnInkNew,
                      grabAfterUrnInk, grabUrnArtNew, grabAfterUrnArt, grabIlkArtNew]
                      using hIlkArtNeg))
                  exact hrev.reEquivExecutionRevert hcode (vatDispatchGrab hsel) hdecode
                    hbody
              · have hInkOldEq :
                    solcSlotWord σ_evm I (grabUrnInkSlot I) =
                      solcSlotWord σ_solm I (grabUrnInkSlot I) :=
                    accountMapEquiv_storage_findD hAccounts I.codeOwner
                      (grabUrnInkSlot I) ⟨0⟩
                have hInkNewEq : grabUrnInkNew σ_evm I = grabUrnInkNew σ_solm I := by
                  simp [grabUrnInkNew, hInkOldEq]
                have hAfterInk :
                    accountMapEquiv (grabAfterUrnInk σ_evm I)
                      (grabAfterUrnInk σ_solm I) := by
                  simp [grabAfterUrnInk, hInkNewEq,
                    accountMapEquiv_sstoreAccountMap I.codeOwner (grabUrnInkSlot I)
                      (grabUrnInkNew σ_solm I) hAccounts]
                have hArtOldEq :
                    solcSlotWord (grabAfterUrnInk σ_evm I) I (grabUrnArtSlot I) =
                      solcSlotWord (grabAfterUrnInk σ_solm I) I (grabUrnArtSlot I) :=
                    accountMapEquiv_storage_findD hAfterInk I.codeOwner
                      (grabUrnArtSlot I) ⟨0⟩
                have hArtNewEq : grabUrnArtNew σ_evm I = grabUrnArtNew σ_solm I := by
                  simp [grabUrnArtNew, hArtOldEq]
                have hInkNegSolm : grabInkNegOk σ_solm I := by
                  simpa [grabInkNegOk, hInkOldEq, hInkNewEq] using hInkNeg
                have hInkPosSolm : grabInkPosOk σ_solm I := by
                  simpa [grabInkPosOk, hInkOldEq, hInkNewEq] using hInkPos
                have hUrnArtNegSolm : grabUrnArtNegOk σ_solm I := by
                  simpa [grabUrnArtNegOk, hArtOldEq, hArtNewEq] using hUrnArtNeg
                have hUrnArtPosFailSolm : ¬ grabUrnArtPosOk σ_solm I := by
                  intro hUrnArtPosSolm
                  exact hUrnArtPos (by
                    simpa [grabUrnArtPosOk, hArtOldEq, hArtNewEq] using
                      hUrnArtPosSolm)
                have hInkGuardNeg :
                    0 ≤ grabDinkInt I ∨
                      (grabUrnInkNew σ_solm I).toNat ≤
                        (vatSlotWord (grabUrnInkSlot I) σ_solm I).toNat := by
                  exact grabDinkAddGuardNegCond (by
                    simpa [grabInkNegOk, grabUrnInkNew, vatSlotWord] using hInkNegSolm)
                have hInkGuardPos :
                    grabDinkInt I ≤ 0 ∨
                      (vatSlotWord (grabUrnInkSlot I) σ_solm I).toNat ≤
                        (grabUrnInkNew σ_solm I).toNat := by
                  exact grabDinkAddGuardPosCond (by
                    simpa [grabInkPosOk, grabUrnInkNew, vatSlotWord] using hInkPosSolm)
                have hArtGuardNeg :
                    0 ≤ grabDartInt I ∨
                      (grabUrnArtNew σ_solm I).toNat ≤
                        (solcSlotWord (grabAfterUrnInk σ_solm I) I
                          (grabUrnArtSlot I)).toNat := by
                  exact grabDartAddGuardNegCond (by
                    simpa [grabUrnArtNegOk, grabUrnArtNew] using hUrnArtNegSolm)
                have hArtGuardPos :
                    0 < grabDartInt I ∧
                      (grabUrnArtNew σ_solm I).toNat <
                        (solcSlotWord (grabAfterUrnInk σ_solm I) I
                          (grabUrnArtSlot I)).toNat := by
                  exact signedAddGuardPosFalseCond_of_word
                    (grabDartInt_lo I) (grabDartInt_hi I) (grabDartInt_mod_word I)
                    (by
                      intro h
                      exact hUrnArtPosFailSolm (by
                        simpa [grabUrnArtPosOk, grabUrnArtNew] using h))
                have hbody :=
                  vatGrabSourceBodyUrnArtRevertGuardPos
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                    (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    hwv hauthSolm hsz196 hInkGuardNeg hInkGuardPos hArtGuardNeg
                    hArtGuardPos
                have hmemAuth :
                    (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
                  twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
                obtain ⟨_, _, hInk⟩ := RD.vatGrabUrnInkAddSuccess
                  (h := hafterAuth) hmemAuth
                  (by simpa [grabUrnInkNew] using hInkNeg)
                  (by simpa [grabUrnInkNew] using hInkPos)
                have hrev := RD.vatGrabUrnArtAddRevert
                  (h := by simpa [grabUrnInkNew] using hInk) hperm
                  (Or.inr ⟨
                    (by simpa [grabUrnArtNegOk, grabUrnInkNew, grabAfterUrnInk,
                      grabUrnArtNew] using hUrnArtNeg),
                    (by simpa [grabUrnArtPosOk, grabUrnInkNew, grabAfterUrnInk,
                      grabUrnArtNew] using hUrnArtPos)⟩)
                exact hrev.reEquivExecutionRevert hcode (vatDispatchGrab hsel) hdecode
                  hbody
            · have hInkOldEq :
                  solcSlotWord σ_evm I (grabUrnInkSlot I) =
                    solcSlotWord σ_solm I (grabUrnInkSlot I) :=
                  accountMapEquiv_storage_findD hAccounts I.codeOwner
                    (grabUrnInkSlot I) ⟨0⟩
              have hInkNewEq : grabUrnInkNew σ_evm I = grabUrnInkNew σ_solm I := by
                simp [grabUrnInkNew, hInkOldEq]
              have hAfterInk :
                  accountMapEquiv (grabAfterUrnInk σ_evm I)
                    (grabAfterUrnInk σ_solm I) := by
                simp [grabAfterUrnInk, hInkNewEq,
                  accountMapEquiv_sstoreAccountMap I.codeOwner (grabUrnInkSlot I)
                    (grabUrnInkNew σ_solm I) hAccounts]
              have hArtOldEq :
                  solcSlotWord (grabAfterUrnInk σ_evm I) I (grabUrnArtSlot I) =
                    solcSlotWord (grabAfterUrnInk σ_solm I) I (grabUrnArtSlot I) :=
                  accountMapEquiv_storage_findD hAfterInk I.codeOwner
                    (grabUrnArtSlot I) ⟨0⟩
              have hArtNewEq : grabUrnArtNew σ_evm I = grabUrnArtNew σ_solm I := by
                simp [grabUrnArtNew, hArtOldEq]
              have hInkNegSolm : grabInkNegOk σ_solm I := by
                simpa [grabInkNegOk, hInkOldEq, hInkNewEq] using hInkNeg
              have hInkPosSolm : grabInkPosOk σ_solm I := by
                simpa [grabInkPosOk, hInkOldEq, hInkNewEq] using hInkPos
              have hUrnArtNegFailSolm : ¬ grabUrnArtNegOk σ_solm I := by
                intro hUrnArtNegSolm
                exact hUrnArtNeg (by
                  simpa [grabUrnArtNegOk, hArtOldEq, hArtNewEq] using
                    hUrnArtNegSolm)
              have hInkGuardNeg :
                  0 ≤ grabDinkInt I ∨
                    (grabUrnInkNew σ_solm I).toNat ≤
                      (vatSlotWord (grabUrnInkSlot I) σ_solm I).toNat := by
                exact grabDinkAddGuardNegCond (by
                  simpa [grabInkNegOk, grabUrnInkNew, vatSlotWord] using hInkNegSolm)
              have hInkGuardPos :
                  grabDinkInt I ≤ 0 ∨
                    (vatSlotWord (grabUrnInkSlot I) σ_solm I).toNat ≤
                      (grabUrnInkNew σ_solm I).toNat := by
                exact grabDinkAddGuardPosCond (by
                  simpa [grabInkPosOk, grabUrnInkNew, vatSlotWord] using hInkPosSolm)
              have hArtGuardNeg :
                  grabDartInt I < 0 ∧
                    (solcSlotWord (grabAfterUrnInk σ_solm I) I
                      (grabUrnArtSlot I)).toNat <
                      (grabUrnArtNew σ_solm I).toNat := by
                exact signedAddGuardNegFalseCond_of_word
                  (grabDartInt_lo I) (grabDartInt_hi I) (grabDartInt_mod_word I)
                  (by
                    intro h
                    exact hUrnArtNegFailSolm (by
                      simpa [grabUrnArtNegOk, grabUrnArtNew] using h))
              have hbody :=
                vatGrabSourceBodyUrnArtRevertGuardNeg
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                  (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hwv hauthSolm hsz196 hInkGuardNeg hInkGuardPos hArtGuardNeg
              have hmemAuth :
                  (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
                twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
              obtain ⟨_, _, hInk⟩ := RD.vatGrabUrnInkAddSuccess
                (h := hafterAuth) hmemAuth
                (by simpa [grabUrnInkNew] using hInkNeg)
                (by simpa [grabUrnInkNew] using hInkPos)
              have hrev := RD.vatGrabUrnArtAddRevert
                (h := by simpa [grabUrnInkNew] using hInk) hperm
                (Or.inl (by simpa [grabUrnArtNegOk, grabUrnInkNew, grabAfterUrnInk,
                  grabUrnArtNew] using hUrnArtNeg))
              exact hrev.reEquivExecutionRevert hcode (vatDispatchGrab hsel) hdecode hbody
          · have hInkOldEq :
                solcSlotWord σ_evm I (grabUrnInkSlot I) =
                  solcSlotWord σ_solm I (grabUrnInkSlot I) :=
                accountMapEquiv_storage_findD hAccounts I.codeOwner
                  (grabUrnInkSlot I) ⟨0⟩
            have hInkNewEq : grabUrnInkNew σ_evm I = grabUrnInkNew σ_solm I := by
              simp [grabUrnInkNew, hInkOldEq]
            have hInkNegSolm : grabInkNegOk σ_solm I := by
              simpa [grabInkNegOk, hInkOldEq, hInkNewEq] using hInkNeg
            have hInkPosFailSolm : ¬ grabInkPosOk σ_solm I := by
              intro hInkPosSolm
              exact hInkPos (by
                simpa [grabInkPosOk, hInkOldEq, hInkNewEq] using hInkPosSolm)
            have hguardNeg :
                0 ≤ grabDinkInt I ∨
                  (grabUrnInkNew σ_solm I).toNat ≤
                    (vatSlotWord (grabUrnInkSlot I) σ_solm I).toNat := by
              exact grabDinkAddGuardNegCond (by
                simpa [grabInkNegOk, grabUrnInkNew, vatSlotWord] using hInkNegSolm)
            have hguardPos :
                0 < grabDinkInt I ∧
                  (grabUrnInkNew σ_solm I).toNat <
                    (vatSlotWord (grabUrnInkSlot I) σ_solm I).toNat := by
              exact signedAddGuardPosFalseCond_of_word
                (grabDinkInt_lo I) (grabDinkInt_hi I) (grabDinkInt_mod_word I)
                (by
                  intro h
                  exact hInkPosFailSolm (by
                    simpa [grabInkPosOk, grabUrnInkNew, vatSlotWord] using h))
            have hbody :=
              vatGrabSourceBodyUrnInkRevertGuardPos
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hauthSolm hsz196 hguardNeg hguardPos
            have hmemAuth :
                (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
              twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
            have hrev := RD.vatGrabUrnInkAddRevert
              (h := hafterAuth) hmemAuth
              (Or.inr ⟨
                (by simpa [grabInkNegOk, grabUrnInkNew] using hInkNeg),
                (by simpa [grabInkPosOk, grabUrnInkNew] using hInkPos)⟩)
            exact hrev.reEquivExecutionRevert hcode (vatDispatchGrab hsel) hdecode hbody
        · have hInkOldEq :
              solcSlotWord σ_evm I (grabUrnInkSlot I) =
                solcSlotWord σ_solm I (grabUrnInkSlot I) :=
              accountMapEquiv_storage_findD hAccounts I.codeOwner
                (grabUrnInkSlot I) ⟨0⟩
          have hInkNewEq : grabUrnInkNew σ_evm I = grabUrnInkNew σ_solm I := by
            simp [grabUrnInkNew, hInkOldEq]
          have hInkNegFailSolm : ¬ grabInkNegOk σ_solm I := by
            intro hInkNegSolm
            exact hInkNeg (by
              simpa [grabInkNegOk, hInkOldEq, hInkNewEq] using hInkNegSolm)
          have hguardNeg :
              grabDinkInt I < 0 ∧
                (vatSlotWord (grabUrnInkSlot I) σ_solm I).toNat <
                  (grabUrnInkNew σ_solm I).toNat := by
            exact signedAddGuardNegFalseCond_of_word
              (grabDinkInt_lo I) (grabDinkInt_hi I) (grabDinkInt_mod_word I)
              (by
                intro h
                exact hInkNegFailSolm (by
                  simpa [grabInkNegOk, grabUrnInkNew, vatSlotWord] using h))
          have hbody :=
            vatGrabSourceBodyUrnInkRevertGuardNeg
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
              (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hauthSolm hsz196 hguardNeg
          have hmemAuth :
              (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
            twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
          have hrev := RD.vatGrabUrnInkAddRevert
            (h := hafterAuth) hmemAuth
            (Or.inl (by simpa [grabInkNegOk, grabUrnInkNew] using hInkNeg))
          exact hrev.reEquivExecutionRevert hcode (vatDispatchGrab hsel) hdecode hbody
    · exact vatGrabBodyCoreUnauthorized hcode hsize hwv hsz196 hauth
        (vatDispatchGrab hsel) hdecode hreach hAccounts
  · have hshort : I.calldata.size < 196 := by omega
    exact vatGrabBodyCoreDecodeFailed_short hcode hsize hsz4 hshort hsel hreach

end Benchmarks.Dss.Vat

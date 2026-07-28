import Benchmarks.UniswapV3Pool.Slot0

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

abbrev observationsUint56Mask : UInt256 :=
  UInt256.ofNat (2 ^ 56 - 1)

def observationsSint56Value (w : UInt256) : Int :=
  let m := w.toNat % EVM.twoPow 56
  if m < EVM.twoPow 55 then (m : Int) else (m : Int) - (EVM.twoPow 56 : Int)

theorem observationsUint56Mask_toNat :
    observationsUint56Mask.toNat = 2 ^ 56 - 1 := by
  exact ulit_toNat' _ (by norm_num [UInt256.size])

private theorem signextend_six_norm (w : UInt256) : UInt256.signextend ⟨6⟩ w =
    if UInt256.land w (UInt256.ofNat (2 ^ 55)) = ⟨0⟩ then
      UInt256.land w (UInt256.ofNat (2 ^ 55 - 1))
    else UInt256.lor w (UInt256.ofNat (UInt256.size - 2 ^ 55)) := by
  unfold UInt256.signextend
  rw [if_pos (by native_decide : (⟨6⟩ : UInt256).toNat ≤ 31)]
  have htest : (⟨6⟩ : UInt256) * ⟨8⟩ + ⟨7⟩ = ⟨55⟩ := by native_decide
  simp only [htest]
  have hsign : (⟨1⟩ : UInt256) <<< (⟨55⟩ : UInt256) = UInt256.ofNat (2 ^ 55) := by
    native_decide
  rw [hsign]
  have hsub1 : UInt256.ofNat (2 ^ 55) - ⟨1⟩ = UInt256.ofNat (2 ^ 55 - 1) := by
    native_decide
  have hsub2 : UInt256.size.toUInt256 - UInt256.ofNat (2 ^ 55) =
      UInt256.ofNat (UInt256.size - 2 ^ 55) := by
    native_decide
  rw [hsub1, hsub2]
  change (if UInt256.land w (UInt256.ofNat (2 ^ 55)) ≠ ⟨0⟩ then
      UInt256.lor w (UInt256.ofNat (UInt256.size - 2 ^ 55))
    else UInt256.land w (UInt256.ofNat (2 ^ 55 - 1))) = _
  by_cases hzero : UInt256.land w (UInt256.ofNat (2 ^ 55)) = ⟨0⟩
  · rw [if_neg (by exact not_not.mpr hzero), if_pos hzero]
  · rw [if_pos hzero, if_neg hzero]

private theorem signextend_six_sign_bit_zero (w : UInt256)
    (hm : w.toNat % EVM.twoPow 56 < EVM.twoPow 55) :
    UInt256.land w (UInt256.ofNat (2 ^ 55)) = ⟨0⟩ := by
  apply u256_inj
  rw [u256_land_toNat]
  have hbitm : (w.toNat % EVM.twoPow 56).testBit 55 = false := by
    exact Nat.testBit_lt_two_pow (x := w.toNat % EVM.twoPow 56) (i := 55) hm
  change (w.toNat % 2 ^ 56).testBit 55 = false at hbitm
  rw [Nat.testBit_mod_two_pow] at hbitm
  have hbitw : w.toNat.testBit 55 = false := by simpa using hbitm
  rw [show (UInt256.ofNat (2 ^ 55)).toNat = 2 ^ 55 by
    exact ulit_toNat' _ (by norm_num [UInt256.size])]
  change (w.toNat &&& 2 ^ 55) % UInt256.size = (⟨0⟩ : UInt256).toNat
  rw [Nat.and_two_pow, hbitw]
  norm_num

private theorem signextend_six_sign_bit_ne_zero (w : UInt256)
    (hm : ¬ w.toNat % EVM.twoPow 56 < EVM.twoPow 55) :
    UInt256.land w (UInt256.ofNat (2 ^ 55)) ≠ ⟨0⟩ := by
  intro hzero
  have hmhi : w.toNat % EVM.twoPow 56 < EVM.twoPow 56 :=
    Nat.mod_lt _ (by norm_num [EVM.twoPow])
  have hmge : EVM.twoPow 55 ≤ w.toNat % EVM.twoPow 56 := by omega
  have hdiv : (w.toNat % EVM.twoPow 56) / EVM.twoPow 55 = 1 := by
    apply Nat.div_eq_of_lt_le (k := 1)
    · simpa [EVM.twoPow] using hmge
    · simpa [EVM.twoPow] using hmhi
  have hbitm : (w.toNat % EVM.twoPow 56).testBit 55 = true := by
    simp [Nat.testBit, Nat.shiftRight_eq_div_pow, EVM.twoPow]
    have hdiv' : w.toNat % 72057594037927936 / 36028797018963968 = 1 := by
      simpa [EVM.twoPow] using hdiv
    rw [hdiv']
  change (w.toNat % 2 ^ 56).testBit 55 = true at hbitm
  rw [Nat.testBit_mod_two_pow] at hbitm
  have hbitw : w.toNat.testBit 55 = true := by simpa using hbitm
  have htoNat := congrArg UInt256.toNat hzero
  rw [u256_land_toNat] at htoNat
  rw [show (UInt256.ofNat (2 ^ 55)).toNat = 2 ^ 55 by
    exact ulit_toNat' _ (by norm_num [UInt256.size])] at htoNat
  change (w.toNat &&& 2 ^ 55) % UInt256.size = (⟨0⟩ : UInt256).toNat at htoNat
  rw [Nat.and_two_pow, hbitw] at htoNat
  norm_num [UInt256.size] at htoNat

private theorem nat_lor_high_mask_55 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.lor n (2 ^ 256 - 2 ^ 55) = n % 2 ^ 55 + (2 ^ 256 - 2 ^ 55) := by
  have hmask : 2 ^ 256 - 2 ^ 55 = (2 ^ (256 - 55) - 1) <<< 55 := by
    rw [Nat.shiftLeft_eq]
    norm_num [Nat.pow_add]
  rw [hmask]
  rw [Nat.shiftLeft_eq]
  rw [← nat_lor_shift_add (n % 2 ^ 55) (2 ^ (256 - 55) - 1) 55
    (Nat.mod_lt _ (by norm_num))]
  apply Nat.eq_of_testBit_eq
  intro i
  change (n ||| ((2 ^ (256 - 55) - 1) * 2 ^ 55)).testBit i =
    ((n % 2 ^ 55) ||| ((2 ^ (256 - 55) - 1) * 2 ^ 55)).testBit i
  rw [Nat.testBit_or, Nat.testBit_or]
  rw [show (2 ^ (256 - 55) - 1) * 2 ^ 55 =
      (2 ^ (256 - 55) - 1) <<< 55 by rw [Nat.shiftLeft_eq]]
  rw [testBit_shiftLeft]
  by_cases hi55 : i < 55
  · rw [if_pos hi55]
    conv_rhs => rw [Nat.testBit_mod_two_pow]
    simp [hi55]
  · rw [if_neg hi55]
    rw [Nat.testBit_two_pow_sub_one]
    by_cases hi256 : i < 256
    · have hlt201 : i - 55 < 256 - 55 := by omega
      rw [decide_eq_true hlt201]
      simp
    · have hnbit : n.testBit i = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have hmodbit : (n % 2 ^ 55).testBit i = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 55))
            (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have hnot201 : ¬ i - 55 < 256 - 55 := by omega
      rw [decide_eq_false hnot201, hnbit, hmodbit]

private theorem wordOfInt_sint56_neg_toNat (m : Nat) (hmhi : m < EVM.twoPow 56) :
    (EVM.wordOfInt ((m : Int) - (EVM.twoPow 56 : Int))).toNat =
      UInt256.size - (EVM.twoPow 56 - m) := by
  have hneg : ((m : Int) - (EVM.twoPow 56 : Int)) < 0 := by
    norm_num [EVM.twoPow] at hmhi ⊢
    omega
  have hnatAbs : ((m : Int) - (EVM.twoPow 56 : Int)).natAbs = EVM.twoPow 56 - m := by
    norm_num [EVM.twoPow] at hmhi ⊢
    omega
  have hdiffPos : EVM.twoPow 56 - m ≠ 0 := by
    norm_num [EVM.twoPow] at hmhi ⊢
    omega
  have hdiffLt : EVM.twoPow 56 - m < EVM.wordModulus := by
    norm_num [EVM.wordModulus, EVM.twoPow] at hmhi ⊢
    omega
  unfold EVM.wordOfInt
  rw [if_pos hneg]
  rw [hnatAbs, Nat.mod_eq_of_lt hdiffLt, if_neg hdiffPos]
  change (UInt256.ofNat (EVM.wordModulus - (EVM.twoPow 56 - m))).toNat = _
  rw [ulit_toNat']
  · simp [EVM.wordModulus, EVM.twoPow, UInt256.size]
  · norm_num [EVM.wordModulus, EVM.twoPow, UInt256.size] at hmhi ⊢
    omega

theorem wordOfInt_sint56Value_eq_signextend_six (w : UInt256) :
    EVM.wordOfInt (observationsSint56Value w) = UInt256.signextend ⟨6⟩ w := by
  apply u256_inj
  rw [signextend_six_norm]
  unfold observationsSint56Value
  let m := w.toNat % EVM.twoPow 56
  have hmdef : m = w.toNat % EVM.twoPow 56 := rfl
  have hmhi : m < EVM.twoPow 56 := by
    rw [hmdef]
    exact Nat.mod_lt _ (by norm_num [EVM.twoPow])
  have hwlt : w.toNat < UInt256.size := by
    simp [UInt256.toNat]
  by_cases h : m < EVM.twoPow 55
  · have hzero : UInt256.land w (UInt256.ofNat (2 ^ 55)) = ⟨0⟩ := by
      apply signextend_six_sign_bit_zero
      rwa [← hmdef]
    rw [if_pos hzero]
    have hval :
        (let m := w.toNat % EVM.twoPow 56
         if m < EVM.twoPow 55 then (m : Int) else (m : Int) - (EVM.twoPow 56 : Int)) =
          (m : Int) := by
      dsimp
      have h' : w.toNat % EVM.twoPow 56 < EVM.twoPow 55 := by rwa [← hmdef]
      rw [if_pos h']
      omega
    rw [hval]
    have hword : (EVM.wordOfInt (m : Int)).toNat = m := by
      unfold EVM.wordOfInt
      rw [if_neg (by omega)]
      unfold EVM.word EVM.uintN UInt256.toNat
      change m % EVM.twoPow 256 = m
      apply Nat.mod_eq_of_lt
      norm_num [EVM.twoPow] at hmhi ⊢
      omega
    rw [hword]
    rw [u256_land_toNat]
    rw [show (UInt256.ofNat (2 ^ 55 - 1)).toNat = 2 ^ 55 - 1 by
      exact ulit_toNat' _ (by norm_num [UInt256.size])]
    change m = Nat.land w.toNat (2 ^ 55 - 1) % UInt256.size
    rw [nat_land_mask_eq_mod]
    have hmdef' : m = w.toNat % 2 ^ 56 := by simpa [EVM.twoPow] using hmdef
    have hmod55 : w.toNat % 2 ^ 55 = m := by
      have hmod56 : w.toNat % 2 ^ 56 = m := hmdef'.symm
      rw [← Nat.mod_mod_of_dvd (a := w.toNat) (show 2 ^ 55 ∣ 2 ^ 56 by norm_num)]
      rw [hmod56]
      exact Nat.mod_eq_of_lt (by simpa [EVM.twoPow] using h)
    rw [hmod55]
    rw [Nat.mod_eq_of_lt (by
      norm_num [EVM.twoPow, UInt256.size] at hmhi ⊢
      omega)]
  · have hne : UInt256.land w (UInt256.ofNat (2 ^ 55)) ≠ ⟨0⟩ := by
      apply signextend_six_sign_bit_ne_zero
      rwa [← hmdef]
    rw [if_neg hne]
    have hval :
        (let m := w.toNat % EVM.twoPow 56
         if m < EVM.twoPow 55 then (m : Int) else (m : Int) - (EVM.twoPow 56 : Int)) =
          (m : Int) - (EVM.twoPow 56 : Int) := by
      dsimp
      have h' : ¬ w.toNat % EVM.twoPow 56 < EVM.twoPow 55 := by
        intro hh
        exact h (by rwa [hmdef])
      rw [if_neg h']
      omega
    rw [hval]
    have hword := wordOfInt_sint56_neg_toNat m hmhi
    rw [hword]
    rw [u256_lor_toNat]
    rw [show (UInt256.ofNat (UInt256.size - 2 ^ 55)).toNat =
        UInt256.size - 2 ^ 55 by
      exact ulit_toNat' _ (by norm_num [UInt256.size])]
    have hlor := nat_lor_high_mask_55 w.toNat (by simpa [UInt256.size] using hwlt)
    change UInt256.size - (EVM.twoPow 56 - m) =
      (Nat.lor w.toNat (2 ^ 256 - 2 ^ 55)) % UInt256.size
    rw [hlor]
    have hmdef' : m = w.toNat % 2 ^ 56 := by simpa [EVM.twoPow] using hmdef
    have hmod55 : w.toNat % 2 ^ 55 = m - 2 ^ 55 := by
      have hge : 2 ^ 55 ≤ m := by
        have hnot : ¬ m < 2 ^ 55 := by simpa [EVM.twoPow] using h
        omega
      have hmhi' : m < 2 ^ 56 := by simpa [EVM.twoPow] using hmhi
      have hmod56 : w.toNat % 2 ^ 56 = m := hmdef'.symm
      rw [← Nat.mod_mod_of_dvd (a := w.toNat) (show 2 ^ 55 ∣ 2 ^ 56 by norm_num)]
      rw [hmod56]
      rw [Nat.mod_eq_sub_mod hge]
      rw [Nat.mod_eq_of_lt (by omega : m - 2 ^ 55 < 2 ^ 55)]
    rw [hmod55]
    norm_num [UInt256.size, EVM.twoPow] at h hmhi ⊢
    omega

theorem observationsSint56Value_mask (w : UInt256) :
    observationsSint56Value (UInt256.land w observationsUint56Mask) =
      observationsSint56Value w := by
  unfold observationsSint56Value
  have hmod : (UInt256.land w observationsUint56Mask).toNat % EVM.twoPow 56 =
      w.toNat % EVM.twoPow 56 := by
    rw [uland_toNat, observationsUint56Mask_toNat]
    change Nat.land w.toNat (2 ^ 56 - 1) % EVM.twoPow 56 =
      w.toNat % EVM.twoPow 56
    rw [nat_land_mask_eq_mod]
    simp [EVM.twoPow]
  rw [hmod]

theorem observationsTickRawValue_wordOfInt (w : UInt256) :
    EVM.wordOfInt (observationsSint56Value (UInt256.land w observationsUint56Mask)) =
      UInt256.signextend ⟨6⟩ w := by
  rw [observationsSint56Value_mask]
  exact wordOfInt_sint56Value_eq_signextend_six w

theorem observationsSint56Value_ge (w : UInt256) :
    -(2 ^ 55 : Int) ≤ observationsSint56Value w := by
  unfold observationsSint56Value
  by_cases h : w.toNat % EVM.twoPow 56 < EVM.twoPow 55
  · rw [if_pos h]
    exact le_trans (by norm_num : -(2 ^ 55 : Int) ≤ 0) (Int.natCast_nonneg _)
  · rw [if_neg h]
    have hmhi := Nat.mod_lt w.toNat (by norm_num [EVM.twoPow] : 0 < EVM.twoPow 56)
    norm_num [EVM.twoPow] at h hmhi ⊢
    omega

theorem observationsSint56Value_lt (w : UInt256) :
    observationsSint56Value w < (2 ^ 55 : Int) := by
  unfold observationsSint56Value
  by_cases h : w.toNat % EVM.twoPow 56 < EVM.twoPow 55
  · rw [if_pos h]
    norm_num [EVM.twoPow] at h ⊢
    omega
  · rw [if_neg h]
    have hmhi := Nat.mod_lt w.toNat (by norm_num [EVM.twoPow] : 0 < EVM.twoPow 56)
    norm_num [EVM.twoPow] at h hmhi ⊢
    omega

private theorem observationsWordOfIntNeg_toNat (i : Int) (hneg : i < 0)
    (hle : i.natAbs < EVM.wordModulus) :
    (EVM.wordOfInt i).toNat = UInt256.size - i.natAbs := by
  have hdiffPos : i.natAbs ≠ 0 := by
    intro h
    have : i = 0 := by omega
    omega
  have hpos : 0 < i.natAbs := Nat.pos_of_ne_zero hdiffPos
  unfold EVM.wordOfInt
  rw [if_pos hneg]
  rw [Nat.mod_eq_of_lt hle, if_neg hdiffPos]
  change (UInt256.ofNat (EVM.wordModulus - i.natAbs)).toNat = UInt256.size - i.natAbs
  rw [ulit_toNat']
  · rw [show EVM.wordModulus = UInt256.size by native_decide]
  · rw [show EVM.wordModulus = UInt256.size by native_decide]
    exact Nat.sub_lt (by native_decide : 0 < UInt256.size) hpos

private theorem observationsSint56Value_wordOfInt (i : Int)
    (hge : -(2 ^ 55) ≤ i) (hlt : i < 2 ^ 55) :
    observationsSint56Value (EVM.wordOfInt i) = i := by
  unfold observationsSint56Value
  by_cases h0 : 0 ≤ i
  · have hword : EVM.wordOfInt i = EVM.word i.toNat := wordOfInt_nonneg i h0
    rw [hword]
    have hltNat : i.toNat < EVM.twoPow 55 := by
      exact (Int.toNat_lt h0).2 (by simpa [EVM.twoPow] using hlt)
    have hto : (EVM.word i.toNat).toNat = i.toNat := by
      unfold EVM.word EVM.uintN UInt256.toNat
      simp only
      show i.toNat % EVM.twoPow 256 = i.toNat
      rw [Nat.mod_eq_of_lt]
      norm_num [EVM.twoPow, UInt256.size] at hltNat ⊢
      omega
    rw [hto]
    have hmod : i.toNat % EVM.twoPow 56 = i.toNat := by
      apply Nat.mod_eq_of_lt
      norm_num [EVM.twoPow] at hltNat ⊢
      omega
    rw [hmod]
    rw [if_pos]
    · exact Int.toNat_of_nonneg h0
    · simpa [EVM.twoPow] using hltNat
  · have hneg : i < 0 := by omega
    have hrle : i.natAbs ≤ EVM.twoPow 55 := by
      have habs : (i.natAbs : Int) = -i := Int.ofNat_natAbs_of_nonpos (by omega)
      have : (i.natAbs : Int) ≤ (EVM.twoPow 55 : Int) := by
        rw [habs]
        norm_num [EVM.twoPow] at hge ⊢
        omega
      omega
    have hrpos : 0 < i.natAbs := by
      by_contra hz
      have : i.natAbs = 0 := by omega
      have : i = 0 := by omega
      omega
    have hword := observationsWordOfIntNeg_toNat i hneg (by
      exact lt_of_le_of_lt hrle (by native_decide : EVM.twoPow 55 < EVM.wordModulus))
    rw [hword]
    let r := i.natAbs
    have hrle' : r ≤ EVM.twoPow 55 := by simpa [r] using hrle
    have hrle56 : r ≤ EVM.twoPow 56 := le_trans hrle' (by native_decide)
    have hrpos' : 0 < r := by simpa [r] using hrpos
    have hmodm : (UInt256.size - r) % EVM.twoPow 56 = EVM.twoPow 56 - r := by
      have hEq : UInt256.size - r =
          (UInt256.size - EVM.twoPow 56) + (EVM.twoPow 56 - r) := by
        norm_num [UInt256.size, EVM.twoPow] at hrle56 ⊢
        omega
      rw [hEq, Nat.add_mod]
      have hdiv : (UInt256.size - EVM.twoPow 56) % EVM.twoPow 56 = 0 := by
        native_decide
      have hltSub : EVM.twoPow 56 - r < EVM.twoPow 56 := by omega
      rw [hdiv, Nat.zero_add]
      rw [Nat.mod_eq_of_lt hltSub]
      rw [Nat.mod_eq_of_lt hltSub]
    rw [hmodm]
    rw [if_neg]
    · have habs : (r : Int) = -i := by
        dsimp [r]
        exact Int.ofNat_natAbs_of_nonpos (by omega)
      norm_num [EVM.twoPow] at hrle' ⊢
      omega
    · norm_num [EVM.twoPow] at hrle' hrpos' ⊢
      omega

theorem signextend_six_wordOfInt_observations (i : Int)
    (hge : -(2 ^ 55) ≤ i) (hlt : i < 2 ^ 55) :
    UInt256.signextend ⟨6⟩ (EVM.wordOfInt i) = EVM.wordOfInt i := by
  rw [← wordOfInt_sint56Value_eq_signextend_six (EVM.wordOfInt i)]
  rw [observationsSint56Value_wordOfInt i hge hlt]

theorem observationsSignextendSix_idempotent (w : UInt256) :
    UInt256.signextend ⟨6⟩ (UInt256.signextend ⟨6⟩ w) =
      UInt256.signextend ⟨6⟩ w := by
  let i := observationsSint56Value w
  have hword : EVM.wordOfInt i = UInt256.signextend ⟨6⟩ w := by
    simpa [i] using wordOfInt_sint56Value_eq_signextend_six w
  rw [← hword]
  exact signextend_six_wordOfInt_observations i (observationsSint56Value_ge w)
    (observationsSint56Value_lt w)

end Benchmarks.UniswapV3Pool

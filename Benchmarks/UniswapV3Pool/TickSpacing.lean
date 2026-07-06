import Benchmarks.UniswapV3Pool.Common

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

def tickSpacingSint24Value (w : UInt256) : Int :=
  let m := w.toNat % EVM.twoPow 24
  if m < EVM.twoPow 23 then (m : Int) else (m : Int) - (EVM.twoPow 24 : Int)

private theorem signextend_two_norm (w : UInt256) : UInt256.signextend ⟨2⟩ w =
    if UInt256.land w (UInt256.ofNat (2 ^ 23)) = ⟨0⟩ then
      UInt256.land w (UInt256.ofNat (2 ^ 23 - 1))
    else UInt256.lor w (UInt256.ofNat (UInt256.size - 2 ^ 23)) := by
  unfold UInt256.signextend
  rw [if_pos (by native_decide : (⟨2⟩ : UInt256).toNat ≤ 31)]
  have htest : (⟨2⟩ : UInt256) * ⟨8⟩ + ⟨7⟩ = ⟨23⟩ := by native_decide
  simp only [htest]
  have hsign : (⟨1⟩ : UInt256) <<< (⟨23⟩ : UInt256) = UInt256.ofNat (2 ^ 23) := by
    native_decide
  rw [hsign]
  have hsub1 : UInt256.ofNat (2 ^ 23) - ⟨1⟩ = UInt256.ofNat (2 ^ 23 - 1) := by
    native_decide
  have hsub2 : UInt256.size.toUInt256 - UInt256.ofNat (2 ^ 23) =
      UInt256.ofNat (UInt256.size - 2 ^ 23) := by
    native_decide
  rw [hsub1, hsub2]
  change (if UInt256.land w (UInt256.ofNat (2 ^ 23)) ≠ ⟨0⟩ then
      UInt256.lor w (UInt256.ofNat (UInt256.size - 2 ^ 23))
    else UInt256.land w (UInt256.ofNat (2 ^ 23 - 1))) = _
  by_cases hzero : UInt256.land w (UInt256.ofNat (2 ^ 23)) = ⟨0⟩
  · rw [if_neg (by exact not_not.mpr hzero), if_pos hzero]
  · rw [if_pos hzero, if_neg hzero]

private theorem signextend_two_sign_bit_zero (w : UInt256)
    (hm : w.toNat % EVM.twoPow 24 < EVM.twoPow 23) :
    UInt256.land w (UInt256.ofNat (2 ^ 23)) = ⟨0⟩ := by
  apply u256_inj
  rw [u256_land_toNat]
  have hbitm : (w.toNat % EVM.twoPow 24).testBit 23 = false := by
    exact Nat.testBit_lt_two_pow (x := w.toNat % EVM.twoPow 24) (i := 23) hm
  change (w.toNat % 2 ^ 24).testBit 23 = false at hbitm
  rw [Nat.testBit_mod_two_pow] at hbitm
  have hbitw : w.toNat.testBit 23 = false := by simpa using hbitm
  rw [show (UInt256.ofNat (2 ^ 23)).toNat = 2 ^ 23 by
    exact ulit_toNat' _ (by norm_num [UInt256.size])]
  change (w.toNat &&& 2 ^ 23) % UInt256.size = (⟨0⟩ : UInt256).toNat
  rw [Nat.and_two_pow, hbitw]
  norm_num

private theorem signextend_two_sign_bit_ne_zero (w : UInt256)
    (hm : ¬ w.toNat % EVM.twoPow 24 < EVM.twoPow 23) :
    UInt256.land w (UInt256.ofNat (2 ^ 23)) ≠ ⟨0⟩ := by
  intro hzero
  have hmhi : w.toNat % EVM.twoPow 24 < EVM.twoPow 24 :=
    Nat.mod_lt _ (by norm_num [EVM.twoPow])
  have hmge : EVM.twoPow 23 ≤ w.toNat % EVM.twoPow 24 := by omega
  have hdiv : (w.toNat % EVM.twoPow 24) / EVM.twoPow 23 = 1 := by
    apply Nat.div_eq_of_lt_le (k := 1)
    · simpa [EVM.twoPow] using hmge
    · simpa [EVM.twoPow] using hmhi
  have hbitm : (w.toNat % EVM.twoPow 24).testBit 23 = true := by
    simp [Nat.testBit, Nat.shiftRight_eq_div_pow, EVM.twoPow]
    have hdiv' : w.toNat % 16777216 / 8388608 = 1 := by
      simpa [EVM.twoPow] using hdiv
    rw [hdiv']
  change (w.toNat % 2 ^ 24).testBit 23 = true at hbitm
  rw [Nat.testBit_mod_two_pow] at hbitm
  have hbitw : w.toNat.testBit 23 = true := by simpa using hbitm
  have htoNat := congrArg UInt256.toNat hzero
  rw [u256_land_toNat] at htoNat
  rw [show (UInt256.ofNat (2 ^ 23)).toNat = 2 ^ 23 by
    exact ulit_toNat' _ (by norm_num [UInt256.size])] at htoNat
  change (w.toNat &&& 2 ^ 23) % UInt256.size = (⟨0⟩ : UInt256).toNat at htoNat
  rw [Nat.and_two_pow, hbitw] at htoNat
  norm_num [UInt256.size] at htoNat

private theorem nat_lor_high_mask_23 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.lor n (2 ^ 256 - 2 ^ 23) = n % 2 ^ 23 + (2 ^ 256 - 2 ^ 23) := by
  have hmask : 2 ^ 256 - 2 ^ 23 = (2 ^ (256 - 23) - 1) <<< 23 := by
    rw [Nat.shiftLeft_eq]
    norm_num [Nat.pow_add]
  rw [hmask]
  rw [Nat.shiftLeft_eq]
  rw [← nat_lor_shift_add (n % 2 ^ 23) (2 ^ (256 - 23) - 1) 23
    (Nat.mod_lt _ (by norm_num))]
  apply Nat.eq_of_testBit_eq
  intro i
  change (n ||| ((2 ^ (256 - 23) - 1) * 2 ^ 23)).testBit i =
    ((n % 2 ^ 23) ||| ((2 ^ (256 - 23) - 1) * 2 ^ 23)).testBit i
  rw [Nat.testBit_or, Nat.testBit_or]
  rw [show (2 ^ (256 - 23) - 1) * 2 ^ 23 =
      (2 ^ (256 - 23) - 1) <<< 23 by rw [Nat.shiftLeft_eq]]
  rw [nat_testBit_shiftLeft]
  by_cases hi23 : i < 23
  · rw [if_pos hi23]
    conv_rhs => rw [Nat.testBit_mod_two_pow]
    simp [hi23]
  · rw [if_neg hi23]
    rw [Nat.testBit_two_pow_sub_one]
    by_cases hi256 : i < 256
    · have hlt233 : i - 23 < 256 - 23 := by omega
      rw [decide_eq_true hlt233]
      simp
    · have hnbit : n.testBit i = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have hmodbit : (n % 2 ^ 23).testBit i = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 23))
            (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have hnot233 : ¬ i - 23 < 256 - 23 := by omega
      rw [decide_eq_false hnot233, hnbit, hmodbit]

private theorem wordOfInt_sint24_neg_toNat (m : Nat) (hmhi : m < EVM.twoPow 24) :
    (EVM.wordOfInt ((m : Int) - (EVM.twoPow 24 : Int))).toNat =
      UInt256.size - (EVM.twoPow 24 - m) := by
  have hneg : ((m : Int) - (EVM.twoPow 24 : Int)) < 0 := by
    norm_num [EVM.twoPow] at hmhi ⊢
    omega
  have hnatAbs : ((m : Int) - (EVM.twoPow 24 : Int)).natAbs = EVM.twoPow 24 - m := by
    norm_num [EVM.twoPow] at hmhi ⊢
    omega
  have hdiffPos : EVM.twoPow 24 - m ≠ 0 := by
    norm_num [EVM.twoPow] at hmhi ⊢
    omega
  have hdiffLt : EVM.twoPow 24 - m < EVM.wordModulus := by
    norm_num [EVM.wordModulus, EVM.twoPow] at hmhi ⊢
    omega
  unfold EVM.wordOfInt
  rw [if_pos hneg]
  rw [hnatAbs, Nat.mod_eq_of_lt hdiffLt, if_neg hdiffPos]
  change (UInt256.ofNat (EVM.wordModulus - (EVM.twoPow 24 - m))).toNat = _
  rw [ulit_toNat']
  · simp [EVM.wordModulus, EVM.twoPow, UInt256.size]
  · norm_num [EVM.wordModulus, EVM.twoPow, UInt256.size] at hmhi ⊢
    omega

theorem wordOfInt_sint24Value_eq_signextend_two (w : UInt256) :
    EVM.wordOfInt (tickSpacingSint24Value w) = UInt256.signextend ⟨2⟩ w := by
  apply u256_inj
  rw [signextend_two_norm]
  unfold tickSpacingSint24Value
  let m := w.toNat % EVM.twoPow 24
  have hmdef : m = w.toNat % EVM.twoPow 24 := rfl
  have hmhi : m < EVM.twoPow 24 := by
    rw [hmdef]
    exact Nat.mod_lt _ (by norm_num [EVM.twoPow])
  have hwlt : w.toNat < UInt256.size := by
    simp [UInt256.toNat]
  by_cases h : m < EVM.twoPow 23
  · have hzero : UInt256.land w (UInt256.ofNat (2 ^ 23)) = ⟨0⟩ := by
      apply signextend_two_sign_bit_zero
      rwa [← hmdef]
    rw [if_pos hzero]
    have hval :
        (let m := w.toNat % EVM.twoPow 24
         if m < EVM.twoPow 23 then (m : Int) else (m : Int) - (EVM.twoPow 24 : Int)) =
          (m : Int) := by
      dsimp
      have h' : w.toNat % EVM.twoPow 24 < EVM.twoPow 23 := by rwa [← hmdef]
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
    rw [show (UInt256.ofNat (2 ^ 23 - 1)).toNat = 2 ^ 23 - 1 by
      exact ulit_toNat' _ (by norm_num [UInt256.size])]
    change m = Nat.land w.toNat (2 ^ 23 - 1) % UInt256.size
    rw [nat_land_mask_eq_mod]
    have hmdef' : m = w.toNat % 2 ^ 24 := by simpa [EVM.twoPow] using hmdef
    have hmod23 : w.toNat % 2 ^ 23 = m := by
      have hmod24 : w.toNat % 2 ^ 24 = m := hmdef'.symm
      rw [← Nat.mod_mod_of_dvd (a := w.toNat) (show 2 ^ 23 ∣ 2 ^ 24 by norm_num)]
      rw [hmod24]
      exact Nat.mod_eq_of_lt (by simpa [EVM.twoPow] using h)
    rw [hmod23]
    rw [Nat.mod_eq_of_lt (by
      norm_num [EVM.twoPow, UInt256.size] at hmhi ⊢
      omega)]
  · have hne : UInt256.land w (UInt256.ofNat (2 ^ 23)) ≠ ⟨0⟩ := by
      apply signextend_two_sign_bit_ne_zero
      rwa [← hmdef]
    rw [if_neg hne]
    have hval :
        (let m := w.toNat % EVM.twoPow 24
         if m < EVM.twoPow 23 then (m : Int) else (m : Int) - (EVM.twoPow 24 : Int)) =
          (m : Int) - (EVM.twoPow 24 : Int) := by
      dsimp
      have h' : ¬ w.toNat % EVM.twoPow 24 < EVM.twoPow 23 := by
        intro hh
        exact h (by rwa [hmdef])
      rw [if_neg h']
      omega
    rw [hval]
    have hword := wordOfInt_sint24_neg_toNat m hmhi
    rw [hword]
    rw [u256_lor_toNat]
    rw [show (UInt256.ofNat (UInt256.size - 2 ^ 23)).toNat =
        UInt256.size - 2 ^ 23 by
      exact ulit_toNat' _ (by norm_num [UInt256.size])]
    have hlor := nat_lor_high_mask_23 w.toNat (by simpa [UInt256.size] using hwlt)
    change UInt256.size - (EVM.twoPow 24 - m) =
      (Nat.lor w.toNat (2 ^ 256 - 2 ^ 23)) % UInt256.size
    rw [hlor]
    have hmdef' : m = w.toNat % 2 ^ 24 := by simpa [EVM.twoPow] using hmdef
    have hmod23 : w.toNat % 2 ^ 23 = m - 2 ^ 23 := by
      have hge : 2 ^ 23 ≤ m := by
        have hnot : ¬ m < 2 ^ 23 := by simpa [EVM.twoPow] using h
        omega
      have hmhi' : m < 2 ^ 24 := by simpa [EVM.twoPow] using hmhi
      have hmod24 : w.toNat % 2 ^ 24 = m := hmdef'.symm
      rw [← Nat.mod_mod_of_dvd (a := w.toNat) (show 2 ^ 23 ∣ 2 ^ 24 by norm_num)]
      rw [hmod24]
      rw [Nat.mod_eq_sub_mod hge]
      rw [Nat.mod_eq_of_lt (by omega : m - 2 ^ 23 < 2 ^ 23)]
    rw [hmod23]
    norm_num [UInt256.size, EVM.twoPow] at h hmhi ⊢
    omega

private theorem wordOfInt_neg_toNat (i : Int) (hneg : i < 0)
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

private theorem int_ediv_pow128_natAbs_of_neg (i : Int) (hneg : i < 0) :
    (i / (2 ^ 128 : Int)).natAbs = (i.natAbs - 1) / 2 ^ 128 + 1 := by
  have hq0 : i / (340282366920938463463374607431768211456 : Int) =
      -((-i - 1) / (340282366920938463463374607431768211456 : Int) + 1) := by
    simpa using Int.ediv_of_neg_of_pos (a := i)
      (b := (340282366920938463463374607431768211456 : Int)) hneg (by norm_num)
  have hq : i / (2 ^ 128 : Int) = -((((i.natAbs - 1) / 2 ^ 128 : Nat) : Int) + 1) := by
    norm_num
    rw [hq0]
    have hnum : -i - 1 = ((i.natAbs - 1 : Nat) : Int) := by
      have habs : (i.natAbs : Int) = -i := Int.ofNat_natAbs_of_nonpos (by omega)
      omega
    rw [hnum]
    have hdivNatCast :
        (((i.natAbs - 1) / 340282366920938463463374607431768211456 : Nat) : Int) =
          ((i.natAbs - 1 : Nat) : Int) /
            (340282366920938463463374607431768211456 : Int) := by
      rw [Int.natCast_ediv]
      norm_num
    rw [← hdivNatCast]
    ring
  rw [hq]
  omega

private theorem u256_complement_toNat_of_lt (w : UInt256)
    (h : w.toNat < UInt256.size - 1) :
    (UInt256.complement w).toNat = UInt256.size - (w.toNat + 1) := by
  change (UInt256.sub (⟨0⟩ : UInt256) (w + ⟨1⟩)).toNat = _
  have hadd : (w + ⟨1⟩).toNat = w.toNat + 1 := by
    rw [uadd_toNat]
    change (w.toNat + 1) % UInt256.size = w.toNat + 1
    exact Nat.mod_eq_of_lt (by omega)
  have hpos : (⟨0⟩ : UInt256).toNat < (w + ⟨1⟩).toNat := by
    rw [hadd]
    change 0 < w.toNat + 1
    omega
  rw [usub_toNat_underflow (a := (⟨0⟩ : UInt256)) (b := w + ⟨1⟩) hpos, hadd]
  change UInt256.size + 0 - (w.toNat + 1) = UInt256.size - (w.toNat + 1)
  rfl

private theorem u256_complement_toNat_of_toNat_eq_size_sub (w : UInt256) (n : Nat)
    (hpos : 0 < n) (hlt : n < UInt256.size) (hw : w.toNat = UInt256.size - n) :
    (UInt256.complement w).toNat = n - 1 := by
  by_cases hn1 : n = 1
  · subst hn1
    have hwtop : w.toNat = UInt256.size - 1 := by simpa using hw
    change (UInt256.sub (⟨0⟩ : UInt256) (w + ⟨1⟩)).toNat = 0
    have hadd : (w + ⟨1⟩).toNat = 0 := by
      rw [uadd_toNat, hwtop]
      change (UInt256.size - 1 + 1) % UInt256.size = 0
      rw [show UInt256.size - 1 + 1 = UInt256.size by omega]
      exact Nat.mod_self _
    rw [usub_toNat (a := (⟨0⟩ : UInt256)) (b := w + ⟨1⟩) (by rw [hadd]; rfl),
      hadd]
    rfl
  · have hltw : w.toNat < UInt256.size - 1 := by
      rw [hw]
      omega
    rw [u256_complement_toNat_of_lt w hltw]
    rw [hw]
    have hsum : UInt256.size - n + 1 = UInt256.size - (n - 1) := by omega
    rw [hsum]
    omega

private theorem sar128_wordOfInt_nonneg (i : Int)
    (h0 : 0 ≤ i) (hlt : i < (2 ^ 255 : Int)) :
    UInt256.sar ⟨128⟩ (EVM.wordOfInt i) = EVM.wordOfInt (i / (2 ^ 128 : Int)) := by
  apply u256_inj
  rw [wordOfInt_nonneg i h0]
  have hdiv0 : 0 ≤ i / (2 ^ 128 : Int) := Int.ediv_nonneg h0 (by norm_num)
  rw [wordOfInt_nonneg (i / (2 ^ 128 : Int)) hdiv0]
  unfold UInt256.sar
  have hwordNat : (EVM.word i.toNat).toNat = i.toNat := by
    unfold EVM.word EVM.uintN UInt256.toNat
    change i.toNat % EVM.twoPow 256 = i.toNat
    apply Nat.mod_eq_of_lt
    have hltNat : i.toNat < EVM.twoPow 255 :=
      (Int.toNat_lt h0).2 (by simpa [EVM.twoPow] using hlt)
    norm_num [EVM.twoPow] at hltNat ⊢
    omega
  have hslt : UInt256.sltBool (EVM.word i.toNat) ⟨0⟩ = false := by
    unfold UInt256.sltBool
    rw [hwordNat]
    have hltNat : i.toNat < 2 ^ 255 := (Int.toNat_lt h0).2 hlt
    rw [if_neg (by omega : ¬ 2 ^ 255 ≤ i.toNat)]
    rw [decide_eq_false (show ¬ EVM.word i.toNat < (⟨0⟩ : UInt256) from
      not_lt_of_ge (Nat.zero_le _))]
    simp
  rw [hslt]
  change (UInt256.shiftRight (EVM.word i.toNat) ⟨128⟩).toNat =
    (EVM.word (i / 2 ^ 128).toNat).toNat
  unfold UInt256.shiftRight
  rw [if_neg (by decide : ¬ (⟨128⟩ : UInt256).val ≥ 256)]
  unfold UInt256.toNat
  rw [Fin.shiftRight_val]
  rw [Nat.shiftRight_eq_div_pow]
  have hleft : (EVM.word i.toNat).val.val = i.toNat := by
    simpa [UInt256.toNat] using hwordNat
  rw [hleft]
  have hdivNat : (i / (2 ^ 128 : Int)).toNat = i.toNat / 2 ^ 128 := by
    apply Int.ofNat_inj.mp
    rw [Int.toNat_of_nonneg hdiv0]
    rw [Int.natCast_ediv]
    rw [Int.toNat_of_nonneg h0]
    norm_num
  have hdivNatLiteral :
      (i / (340282366920938463463374607431768211456 : Int)).toNat =
        i.toNat / 2 ^ 128 := by
    simpa using hdivNat
  simp only [EVM.word, EVM.uintN]
  change i.toNat / 2 ^ (128 % UInt256.size) =
    (i / (340282366920938463463374607431768211456 : Int)).toNat % EVM.twoPow 256
  rw [hdivNatLiteral]
  have hltNat : i.toNat < EVM.twoPow 255 :=
    (Int.toNat_lt h0).2 (by simpa [EVM.twoPow] using hlt)
  have hltDiv : i.toNat / 2 ^ 128 < EVM.twoPow 256 := by
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans hltNat (by norm_num [EVM.twoPow]))
  rw [Nat.mod_eq_of_lt hltDiv]
  norm_num [UInt256.size]

private theorem sar128_wordOfInt_neg (i : Int)
    (hneg : i < 0) (hge : -(2 ^ 255 : Int) ≤ i) :
    UInt256.sar ⟨128⟩ (EVM.wordOfInt i) = EVM.wordOfInt (i / (2 ^ 128 : Int)) := by
  apply u256_inj
  have hnpos : 0 < i.natAbs := by
    have : i ≠ 0 := by omega
    exact Int.natAbs_pos.mpr this
  have hnlt : i.natAbs < UInt256.size := by
    have habs : (i.natAbs : Int) = -i := Int.ofNat_natAbs_of_nonpos (by omega)
    have : (i.natAbs : Int) ≤ 2 ^ 255 := by
      rw [habs]
      omega
    norm_num [UInt256.size] at this ⊢
    omega
  have hw : (EVM.wordOfInt i).toNat = UInt256.size - i.natAbs := by
    exact wordOfInt_neg_toNat i hneg (by simpa [EVM.wordModulus] using hnlt)
  unfold UInt256.sar
  have hslt : UInt256.sltBool (EVM.wordOfInt i) ⟨0⟩ = true := by
    unfold UInt256.sltBool
    rw [hw]
    have hsign : 2 ^ 255 ≤ UInt256.size - i.natAbs := by
      have habs : (i.natAbs : Int) = -i := Int.ofNat_natAbs_of_nonpos (by omega)
      have : (i.natAbs : Int) ≤ 2 ^ 255 := by
        rw [habs]
        omega
      norm_num [UInt256.size] at this ⊢
      omega
    rw [if_pos hsign]
    rw [if_neg (by norm_num : ¬ (⟨0⟩ : UInt256).toNat ≥ 2 ^ 255)]
  rw [hslt]
  simp only [if_true]
  change (UInt256.complement
      (UInt256.shiftRight (UInt256.complement (EVM.wordOfInt i)) ⟨128⟩)).toNat =
    (EVM.wordOfInt (i / (2 ^ 128 : Int))).toNat
  let n := i.natAbs
  have hcomp : (UInt256.complement (EVM.wordOfInt i)).toNat = n - 1 := by
    dsimp [n]
    exact u256_complement_toNat_of_toNat_eq_size_sub (EVM.wordOfInt i) i.natAbs
      hnpos hnlt hw
  have hshift :
      (UInt256.shiftRight (UInt256.complement (EVM.wordOfInt i)) ⟨128⟩).toNat =
        (n - 1) / 2 ^ 128 := by
    unfold UInt256.shiftRight
    rw [if_neg (by decide : ¬ (⟨128⟩ : UInt256).val ≥ 256)]
    unfold UInt256.toNat
    rw [Fin.shiftRight_val]
    rw [Nat.shiftRight_eq_div_pow]
    rw [show (UInt256.complement (EVM.wordOfInt i)).val.val =
      (UInt256.complement (EVM.wordOfInt i)).toNat by rfl]
    rw [hcomp]
    norm_num [UInt256.size]
  let m := (n - 1) / 2 ^ 128
  have hmSmall : m < UInt256.size - 1 := by
    dsimp [m, n]
    have hle : (i.natAbs - 1) / 2 ^ 128 ≤ i.natAbs - 1 := Nat.div_le_self _ _
    omega
  have hcomp2 :
      (UInt256.complement
        (UInt256.shiftRight (UInt256.complement (EVM.wordOfInt i)) ⟨128⟩)).toNat =
        UInt256.size - (m + 1) := by
    rw [u256_complement_toNat_of_lt
      (UInt256.shiftRight (UInt256.complement (EVM.wordOfInt i)) ⟨128⟩)]
    · rw [hshift]
    · rw [hshift]
      exact hmSmall
  rw [hcomp2]
  have hquotNeg : i / (2 ^ 128 : Int) < 0 := by
    exact Int.ediv_neg_of_neg_of_pos hneg (by norm_num)
  have hqAbs : (i / (2 ^ 128 : Int)).natAbs = m + 1 := by
    simpa [m, n] using int_ediv_pow128_natAbs_of_neg i hneg
  have hqLt : (i / (2 ^ 128 : Int)).natAbs < EVM.wordModulus := by
    rw [hqAbs]
    dsimp [m, n]
    have hle : (i.natAbs - 1) / 2 ^ 128 ≤ i.natAbs - 1 := Nat.div_le_self _ _
    have hmod : i.natAbs < EVM.wordModulus := by
      simpa [EVM.wordModulus] using hnlt
    omega
  rw [wordOfInt_neg_toNat (i / (2 ^ 128 : Int)) hquotNeg hqLt]
  rw [hqAbs]

theorem sar128_wordOfInt (i : Int)
    (hge : -(2 ^ 255 : Int) ≤ i) (hlt : i < 2 ^ 255) :
    UInt256.sar ⟨128⟩ (EVM.wordOfInt i) = EVM.wordOfInt (i / (2 ^ 128 : Int)) := by
  by_cases h0 : 0 ≤ i
  · exact sar128_wordOfInt_nonneg i h0 hlt
  · exact sar128_wordOfInt_neg i (by omega) hge

private theorem tickSpacingSint24Value_wordOfInt (i : Int)
    (hge : -(2 ^ 23) ≤ i) (hlt : i < 2 ^ 23) :
    tickSpacingSint24Value (EVM.wordOfInt i) = i := by
  unfold tickSpacingSint24Value
  by_cases h0 : 0 ≤ i
  · have hword : EVM.wordOfInt i = EVM.word i.toNat := wordOfInt_nonneg i h0
    rw [hword]
    have hltNat : i.toNat < EVM.twoPow 23 := by
      exact (Int.toNat_lt h0).2 (by simpa [EVM.twoPow] using hlt)
    have hto : (EVM.word i.toNat).toNat = i.toNat := by
      unfold EVM.word EVM.uintN UInt256.toNat
      simp only
      show i.toNat % EVM.twoPow 256 = i.toNat
      rw [Nat.mod_eq_of_lt]
      norm_num [EVM.twoPow, UInt256.size] at hltNat ⊢
      omega
    rw [hto]
    have hmod : i.toNat % EVM.twoPow 24 = i.toNat := by
      apply Nat.mod_eq_of_lt
      norm_num [EVM.twoPow] at hltNat ⊢
      omega
    rw [hmod]
    rw [if_pos]
    · exact Int.toNat_of_nonneg h0
    · simpa [EVM.twoPow] using hltNat
  · have hneg : i < 0 := by omega
    have hrle : i.natAbs ≤ EVM.twoPow 23 := by
      have habs : (i.natAbs : Int) = -i := Int.ofNat_natAbs_of_nonpos (by omega)
      have : (i.natAbs : Int) ≤ (EVM.twoPow 23 : Int) := by
        rw [habs]
        norm_num [EVM.twoPow] at hge ⊢
        omega
      omega
    have hrpos : 0 < i.natAbs := by
      by_contra hz
      have : i.natAbs = 0 := by omega
      have : i = 0 := by omega
      omega
    have hword := wordOfInt_neg_toNat i hneg (by
      exact lt_of_le_of_lt hrle (by native_decide : EVM.twoPow 23 < EVM.wordModulus))
    rw [hword]
    let r := i.natAbs
    have hrle' : r ≤ EVM.twoPow 23 := by simpa [r] using hrle
    have hrle24 : r ≤ EVM.twoPow 24 := le_trans hrle' (by native_decide)
    have hrpos' : 0 < r := by simpa [r] using hrpos
    have hmodm : (UInt256.size - r) % EVM.twoPow 24 = EVM.twoPow 24 - r := by
      have hEq : UInt256.size - r =
          (UInt256.size - EVM.twoPow 24) + (EVM.twoPow 24 - r) := by
        norm_num [UInt256.size, EVM.twoPow] at hrle24 ⊢
        omega
      rw [hEq, Nat.add_mod]
      have hdiv : (UInt256.size - EVM.twoPow 24) % EVM.twoPow 24 = 0 := by
        native_decide
      have hltSub : EVM.twoPow 24 - r < EVM.twoPow 24 := by omega
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

theorem signextend_two_wordOfInt_tickSpacing (i : Int)
    (hge : -(2 ^ 23) ≤ i) (hlt : i < 2 ^ 23) :
    UInt256.signextend ⟨2⟩ (EVM.wordOfInt i) = EVM.wordOfInt i := by
  rw [← wordOfInt_sint24Value_eq_signextend_two (EVM.wordOfInt i)]
  rw [tickSpacingSint24Value_wordOfInt i hge hlt]

theorem wordToElem_int24_wordOfInt (i : Int)
    (hge : -(2 ^ 23) ≤ i) (hlt : i < 2 ^ 23) :
    wordToElem (.int int24Int) (EVM.wordOfInt i) = .int i := by
  unfold wordToElem int24Int
  change Value.int (tickSpacingSint24Value (EVM.wordOfInt i)) = .int i
  rw [tickSpacingSint24Value_wordOfInt i hge hlt]

theorem wordOfInt_int24_inj {i j : Int}
    (hige : -(2 ^ 23) ≤ i) (hilt : i < 2 ^ 23)
    (hjge : -(2 ^ 23) ≤ j) (hjlt : j < 2 ^ 23)
    (h : EVM.wordOfInt i = EVM.wordOfInt j) :
    i = j := by
  have hdecoded := congrArg (wordToElem (.int int24Int)) h
  rw [wordToElem_int24_wordOfInt i hige hilt,
    wordToElem_int24_wordOfInt j hjge hjlt] at hdecoded
  exact Value.int.inj hdecoded

-- LIBRARY CANDIDATE: signed comparison of a bounded `wordOfInt` with zero.
theorem slt_wordOfInt_int24_zero (i : Int)
    (hge : -(2 ^ 23 : Int) ≤ i) (hlt : i < 2 ^ 23) :
    UInt256.slt (EVM.wordOfInt i) ⟨0⟩ = if i < 0 then ⟨1⟩ else ⟨0⟩ := by
  by_cases hneg : i < 0
  · rw [if_pos hneg]
    apply slt_lit_one_high (m := 0)
    · norm_num
    · have hto := wordOfInt_neg_toNat i hneg (by
        have hle : i.natAbs ≤ EVM.twoPow 23 := by
          have habs : (i.natAbs : Int) = -i := Int.ofNat_natAbs_of_nonpos (by omega)
          norm_num [EVM.twoPow] at hge ⊢
          omega
        exact lt_of_le_of_lt hle (by native_decide : EVM.twoPow 23 < EVM.wordModulus))
      rw [hto]
      have hle : i.natAbs ≤ 2 ^ 23 := by
        have habs : (i.natAbs : Int) = -i := Int.ofNat_natAbs_of_nonpos (by omega)
        norm_num at hge ⊢
        omega
      norm_num [UInt256.size] at hle ⊢
      omega
  · rw [if_neg hneg]
    have h0 : 0 ≤ i := by omega
    rw [wordOfInt_nonneg i h0]
    apply slt_lit_zero (m := 0)
    · norm_num
    · simp
    · have hltNat : i.toNat < 2 ^ 23 := (Int.toNat_lt h0).2 hlt
      unfold EVM.word EVM.uintN UInt256.toNat
      simp only
      rw [Nat.mod_eq_of_lt]
      · exact lt_trans hltNat (by norm_num)
      · exact lt_trans hltNat (by norm_num [EVM.twoPow])

-- LIBRARY CANDIDATE: negating a bounded negative signed integer as an EVM word.
theorem zero_sub_wordOfInt_int24_neg (i : Int)
    (hneg : i < 0) (hge : -(2 ^ 23 : Int) ≤ i) :
    UInt256.sub ⟨0⟩ (EVM.wordOfInt i) = EVM.wordOfInt (-i) := by
  apply u256_inj
  have hleAbs : i.natAbs ≤ EVM.twoPow 23 := by
    have habs : (i.natAbs : Int) = -i := Int.ofNat_natAbs_of_nonpos (by omega)
    norm_num [EVM.twoPow] at hge ⊢
    omega
  have hword := wordOfInt_neg_toNat i hneg
    (lt_of_le_of_lt hleAbs (by native_decide : EVM.twoPow 23 < EVM.wordModulus))
  have hwordPos : 0 < (EVM.wordOfInt i).toNat := by
    rw [hword]
    have hpos : 0 < i.natAbs := by
      have : i ≠ 0 := by omega
      exact Int.natAbs_pos.mpr this
    norm_num [UInt256.size] at hleAbs ⊢
    omega
  rw [usub_toNat_underflow (a := (⟨0⟩ : UInt256)) (b := EVM.wordOfInt i) hwordPos]
  rw [hword]
  have hnegNonneg : 0 ≤ -i := by omega
  rw [wordOfInt_nonneg (-i) hnegNonneg]
  unfold EVM.word EVM.uintN UInt256.toNat
  simp only
  rw [Nat.mod_eq_of_lt]
  · have habs : (-i).toNat = i.natAbs := by omega
    rw [habs]
    norm_num [UInt256.size] at hleAbs ⊢
    omega
  · have habs : (-i).toNat = i.natAbs := by omega
    rw [habs]
    exact lt_of_le_of_lt hleAbs (by native_decide : EVM.twoPow 23 < EVM.twoPow 256)

theorem wordOfInt_nonneg_toNat_lt_wordModulus (i : Int)
    (h0 : 0 ≤ i) (hlt : i < EVM.wordModulus) :
    (EVM.wordOfInt i).toNat = i.toNat := by
  rw [wordOfInt_nonneg i h0]
  unfold EVM.word EVM.uintN UInt256.toNat
  simp only
  rw [Nat.mod_eq_of_lt]
  exact (Int.toNat_lt h0).2 hlt

theorem wordOfInt_neg_toNat_lt_wordModulus (i : Int)
    (hneg : i < 0) (hlt : i.natAbs < EVM.wordModulus) :
    (EVM.wordOfInt i).toNat = UInt256.size - i.natAbs := by
  exact wordOfInt_neg_toNat i hneg hlt

theorem tickSpacingSint24Value_ge (w : UInt256) :
    -(2 ^ 23 : Int) ≤ tickSpacingSint24Value w := by
  unfold tickSpacingSint24Value
  by_cases h : w.toNat % EVM.twoPow 24 < EVM.twoPow 23
  · rw [if_pos h]
    exact le_trans (by norm_num : -(2 ^ 23 : Int) ≤ 0) (Int.natCast_nonneg _)
  · rw [if_neg h]
    have hmhi := Nat.mod_lt w.toNat (by norm_num [EVM.twoPow] : 0 < EVM.twoPow 24)
    norm_num [EVM.twoPow] at h hmhi ⊢
    omega

theorem tickSpacingSint24Value_lt (w : UInt256) :
    tickSpacingSint24Value w < (2 ^ 23 : Int) := by
  unfold tickSpacingSint24Value
  by_cases h : w.toNat % EVM.twoPow 24 < EVM.twoPow 23
  · rw [if_pos h]
    norm_num [EVM.twoPow] at h ⊢
    omega
  · rw [if_neg h]
    have hmhi := Nat.mod_lt w.toNat (by norm_num [EVM.twoPow] : 0 < EVM.twoPow 24)
    norm_num [EVM.twoPow] at h hmhi ⊢
    omega

theorem signextend_two_tickSpacing_idempotent (w : UInt256) :
    UInt256.signextend ⟨2⟩ (UInt256.signextend ⟨2⟩ w) =
      UInt256.signextend ⟨2⟩ w := by
  let i := tickSpacingSint24Value w
  have hword : EVM.wordOfInt i = UInt256.signextend ⟨2⟩ w := by
    simpa [i] using wordOfInt_sint24Value_eq_signextend_two w
  rw [← hword]
  exact signextend_two_wordOfInt_tickSpacing i (tickSpacingSint24Value_ge w)
    (tickSpacingSint24Value_lt w)

private theorem int24_natAbs_le {i : Int}
    (hge : -(2 ^ 23 : Int) ≤ i) (hlt : i < 2 ^ 23) :
    i.natAbs ≤ 2 ^ 23 := by
  by_cases hneg : i < 0
  · have habs : (i.natAbs : Int) = -i := Int.ofNat_natAbs_of_nonpos (by omega)
    norm_num at hge hlt ⊢
    omega
  · have h0 : 0 ≤ i := by omega
    have hcast : (i.natAbs : Int) ≤ 2 ^ 23 := by
      have habs : (i.natAbs : Int) = i := Int.natAbs_of_nonneg h0
      rw [habs]
      omega
    exact_mod_cast hcast

-- LIBRARY CANDIDATE: signed comparison of two bounded `wordOfInt` int24 values.
theorem slt_wordOfInt_int24 (i j : Int)
    (hige : -(2 ^ 23 : Int) ≤ i) (hilt : i < 2 ^ 23)
    (hjge : -(2 ^ 23 : Int) ≤ j) (hjlt : j < 2 ^ 23) :
    UInt256.slt (EVM.wordOfInt i) (EVM.wordOfInt j) =
      if i < j then ⟨1⟩ else ⟨0⟩ := by
  have hiAbsLe := int24_natAbs_le hige hilt
  have hjAbsLe := int24_natAbs_le hjge hjlt
  by_cases hi : i < 0
  · have hito := wordOfInt_neg_toNat_lt_wordModulus i hi (by
      exact lt_of_le_of_lt hiAbsLe (by native_decide : 2 ^ 23 < EVM.wordModulus))
    have hiHigh : 2 ^ 255 ≤ (EVM.wordOfInt i).toNat := by
      rw [hito]
      norm_num [UInt256.size] at hiAbsLe ⊢
      omega
    by_cases hj : j < 0
    · have hjto := wordOfInt_neg_toNat_lt_wordModulus j hj (by
        exact lt_of_le_of_lt hjAbsLe (by native_decide : 2 ^ 23 < EVM.wordModulus))
      have hjHigh : 2 ^ 255 ≤ (EVM.wordOfInt j).toNat := by
        rw [hjto]
        norm_num [UInt256.size] at hjAbsLe ⊢
        omega
      unfold UInt256.slt UInt256.sltBool UInt256.fromBool Bool.toUInt256
      rw [if_pos hiHigh, if_pos hjHigh]
      by_cases hij : i < j
      · rw [if_pos hij]
        have hword : EVM.wordOfInt i < EVM.wordOfInt j := by
          show (EVM.wordOfInt i).toNat < (EVM.wordOfInt j).toNat
          rw [hito, hjto]
          have habsI : (i.natAbs : Int) = -i := Int.ofNat_natAbs_of_nonpos (by omega)
          have habsJ : (j.natAbs : Int) = -j := Int.ofNat_natAbs_of_nonpos (by omega)
          norm_num [UInt256.size] at hiAbsLe hjAbsLe ⊢
          omega
        rw [if_pos (decide_eq_true hword)]
        rfl
      · rw [if_neg hij]
        have hword : ¬ EVM.wordOfInt i < EVM.wordOfInt j := by
          intro hword
          have hnat : (EVM.wordOfInt i).toNat < (EVM.wordOfInt j).toNat := hword
          rw [hito, hjto] at hnat
          have habsI : (i.natAbs : Int) = -i := Int.ofNat_natAbs_of_nonpos (by omega)
          have habsJ : (j.natAbs : Int) = -j := Int.ofNat_natAbs_of_nonpos (by omega)
          norm_num [UInt256.size] at hiAbsLe hjAbsLe hnat
          omega
        rw [if_neg (by rw [decide_eq_false hword]; decide)]
        rfl
    · have hj0 : 0 ≤ j := by omega
      have hjto := wordOfInt_nonneg_toNat_lt_wordModulus j hj0 (by
        exact lt_of_lt_of_le hjlt (by native_decide : (2 ^ 23 : Int) ≤ EVM.wordModulus))
      have hjLow : (EVM.wordOfInt j).toNat < 2 ^ 255 := by
        rw [hjto]
        have hjNatLt : j.toNat < 2 ^ 23 := (Int.toNat_lt hj0).2 hjlt
        norm_num at hjNatLt ⊢
        omega
      rw [if_pos (by omega : i < j)]
      unfold UInt256.slt UInt256.sltBool UInt256.fromBool Bool.toUInt256
      rw [if_pos hiHigh, if_neg (by omega : ¬ (EVM.wordOfInt j).toNat ≥ 2 ^ 255)]
      rfl
  · have hi0 : 0 ≤ i := by omega
    have hito := wordOfInt_nonneg_toNat_lt_wordModulus i hi0 (by
      exact lt_of_lt_of_le hilt (by native_decide : (2 ^ 23 : Int) ≤ EVM.wordModulus))
    have hiLow : (EVM.wordOfInt i).toNat < 2 ^ 255 := by
      rw [hito]
      have hiNatLt : i.toNat < 2 ^ 23 := (Int.toNat_lt hi0).2 hilt
      norm_num at hiNatLt ⊢
      omega
    by_cases hj : j < 0
    · have hjto := wordOfInt_neg_toNat_lt_wordModulus j hj (by
        exact lt_of_le_of_lt hjAbsLe (by native_decide : 2 ^ 23 < EVM.wordModulus))
      have hjHigh : 2 ^ 255 ≤ (EVM.wordOfInt j).toNat := by
        rw [hjto]
        norm_num [UInt256.size] at hjAbsLe ⊢
        omega
      rw [if_neg (by omega : ¬ i < j)]
      unfold UInt256.slt UInt256.sltBool UInt256.fromBool Bool.toUInt256
      rw [if_neg (by omega : ¬ (EVM.wordOfInt i).toNat ≥ 2 ^ 255), if_pos hjHigh]
      rfl
    · have hj0 : 0 ≤ j := by omega
      have hjto := wordOfInt_nonneg_toNat_lt_wordModulus j hj0 (by
        exact lt_of_lt_of_le hjlt (by native_decide : (2 ^ 23 : Int) ≤ EVM.wordModulus))
      have hjLow : (EVM.wordOfInt j).toNat < 2 ^ 255 := by
        rw [hjto]
        have hjNatLt : j.toNat < 2 ^ 23 := (Int.toNat_lt hj0).2 hjlt
        norm_num at hjNatLt ⊢
        omega
      unfold UInt256.slt UInt256.sltBool UInt256.fromBool Bool.toUInt256
      rw [if_neg (by omega : ¬ (EVM.wordOfInt i).toNat ≥ 2 ^ 255),
        if_neg (by omega : ¬ (EVM.wordOfInt j).toNat ≥ 2 ^ 255)]
      by_cases hij : i < j
      · rw [if_pos hij]
        have hword : EVM.wordOfInt i < EVM.wordOfInt j := by
          show (EVM.wordOfInt i).toNat < (EVM.wordOfInt j).toNat
          rw [hito, hjto]
          omega
        rw [if_pos (decide_eq_true hword)]
        rfl
      · rw [if_neg hij]
        have hword : ¬ EVM.wordOfInt i < EVM.wordOfInt j := by
          intro hword
          have hnat : (EVM.wordOfInt i).toNat < (EVM.wordOfInt j).toNat := hword
          rw [hito, hjto] at hnat
          omega
        rw [if_neg (by rw [decide_eq_false hword]; decide)]
        rfl

-- LIBRARY CANDIDATE: `SGT a b` is signed `SLT b a`.
theorem sgt_eq_slt_swap (a b : UInt256) :
    UInt256.sgt a b = UInt256.slt b a := by
  unfold UInt256.sgt UInt256.slt UInt256.sgtBool UInt256.sltBool UInt256.fromBool
    Bool.toUInt256
  by_cases ha : a.toNat ≥ 2 ^ 255 <;> by_cases hb : b.toNat ≥ 2 ^ 255
  · rw [if_pos ha, if_pos hb, if_pos hb, if_pos ha]
  · rw [if_pos ha, if_neg hb, if_neg hb, if_pos ha]
  · rw [if_neg ha, if_pos hb, if_pos hb, if_neg ha]
  · rw [if_neg ha, if_neg hb, if_neg hb, if_neg ha]

theorem zero_sub_wordOfInt_int24_neg_toNat (i : Int)
    (hneg : i < 0) (hge : -(2 ^ 23 : Int) ≤ i) :
    (UInt256.sub ⟨0⟩ (EVM.wordOfInt i)).toNat = (-i).toNat := by
  have hleAbs : i.natAbs ≤ EVM.twoPow 23 := by
    have habs : (i.natAbs : Int) = -i := Int.ofNat_natAbs_of_nonpos (by omega)
    norm_num [EVM.twoPow] at hge ⊢
    omega
  have hword := wordOfInt_neg_toNat i hneg
    (lt_of_le_of_lt hleAbs (by native_decide : EVM.twoPow 23 < EVM.wordModulus))
  have hwordPos : 0 < (EVM.wordOfInt i).toNat := by
    rw [hword]
    have hpos : 0 < i.natAbs := by
      have : i ≠ 0 := by omega
      exact Int.natAbs_pos.mpr this
    norm_num [UInt256.size] at hleAbs ⊢
    omega
  rw [usub_toNat_underflow (a := (⟨0⟩ : UInt256)) (b := EVM.wordOfInt i) hwordPos]
  rw [hword]
  have habs : (-i).toNat = i.natAbs := by omega
  rw [habs]
  norm_num [UInt256.size] at hleAbs ⊢
  omega

theorem int24ReturnEncodingInt (i : Int) (hge : -(2 ^ 23) ≤ i) (hlt : i < 2 ^ 23) :
    encodeReturnValue? int24 (.int i) = some (UInt256.toByteArray (EVM.wordOfInt i)) := by
  have hge' : -(Int.ofNat (EVM.twoPow 23)) ≤ i := by
    simpa [EVM.twoPow] using hge
  have hlt' : i < Int.ofNat (EVM.twoPow 23) := by
    simpa [EVM.twoPow] using hlt
  refine scalarReturnEncoding (t := (.int (.sint ⟨24, by decide⟩)))
    (w := EVM.wordOfInt i) rfl ?_ ?_
  · simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
    decide
  · simp only [encodeABIValue?, encodeABIWord?]
    rw [if_neg (by decide : 24 ≠ 0)]
    rw [if_pos]
    · rfl
    · constructor
      · simpa [EVM.twoPow] using hge
      · simpa [EVM.twoPow] using hlt

private theorem uniswapV3PoolPatchPreservesJumpDest10491 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨10491⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched10491 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨10491⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest10491

theorem uniswapV3PoolTickSpacingReachEntry {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 20 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2009⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := uniswapV3PoolReachSelector32
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hword : solcSelectorWord I = uniswapV3PoolSelNat 20 := by
    simpa [uniswapV3PoolSelBytes, uniswapV3PoolSelNat] using
      solcSelectorWord_eq_of_beq I hsz 0xd0 0xc9 0x3a 0x7c
        (uniswapV3PoolSelNat 20) (by native_decide) hsel
  have hgt32 : UInt256.gt (armSelNat code ⟨32⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h43 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨43⟩) hpatch h32 hgt32
  have hgt43 : UInt256.gt (armSelNat code ⟨43⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h54 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨54⟩) hpatch h43 hgt43
  have hgt54 : UInt256.gt (armSelNat code ⟨54⟩) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h114 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨114⟩) hpatch h54 hgt54
  have hmiss19 : (uniswapV3PoolSelBytes 19 == I.calldata.extract 0 4) = false :=
    uniswapV3PoolSelectorMissOfHit I (by native_decide) hsel
  have h125 := uniswapV3PoolSelectorArmMissToOf (i := 19) (next := ⟨125⟩)
    hpatch hsz hmiss19 h114
  have h2009 := uniswapV3PoolSelectorArmHitTo (i := 20) (target := ⟨2009⟩)
    hpatch hsz hsel h125
  exact ⟨_, _, h2009⟩

theorem uniswapV3PoolTickSpacingDecode {v : PoolImmutables} {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
      ((tickspacingTransition v).params.map Param.name)
      (transitionSignature (tickspacingTransition v)).paramTypes I.calldata =
        some (∅ : Store) := by
  simpa [config, tickspacingTransition, transitionSignature] using
    decodeCalldataWithMode_empty_ok (mode := DecodeMode.legacySolc05) (cd := I.calldata) hsz

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolDispatch_tickSpacing {v : PoolImmutables} {cd : ByteArray}
    (hsel : (uniswapV3PoolSelBytes 20 == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some (tickspacingTransition v) := by
  apply dispatchMsg_eq_some_of_split
    (pre := [burnTransition, collectTransition v, collectprotocolTransition v,
      factoryTransition v, feeTransition v, feegrowthglobal0X128Transition,
      feegrowthglobal1X128Transition, flashTransition v,
      increaseobservationcardinalitynextTransition v, initializeTransition, liquidityTransition,
      maxliquiditypertickTransition v, mintTransition v, observationsTransition, observeTransition v,
      positionsTransition, protocolfeesTransition, setfeeprotocolTransition v, slot0Transition,
      snapshotcumulativesinsideTransition v, swapTransition v, tickbitmapTransition])
    (post := [ticksTransition, token0Transition v, token1Transition v])
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, burnSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 17) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, collectSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 10) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, collectProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 15) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, factorySelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 19) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, feeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 22) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal0X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 23) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal1X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 8) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, flashSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 9) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, increaseObservationCardinalityNextSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 5) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, initializeSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 25) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, liquiditySelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 2) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, maxLiquidityPerTickSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 13) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, mintSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 7) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, observationsSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 4) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, observeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 16) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, positionsSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 11) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, protocolFeesSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 3) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, setFeeProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 14) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, slot0SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 6) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, snapshotCumulativesInsideSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 18) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, swapSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 1) (j := 20)
          (by native_decide) hsel
    · rw [selectorOf, tickBitmapSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 12) (j := 20)
          (by native_decide) hsel
  · rw [selectorOf, tickSpacingSelectorBytes v]
    simpa [uniswapV3PoolSelBytes] using hsel

theorem uniswapV3PoolTickSpacingPatchWord {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    code.extract 10493 10525 = UInt256.toByteArray (EVM.wordOfInt v.tickSpacing) := by
  let value := UInt256.toByteArray (EVM.wordOfInt v.tickSpacing)
  let pre : List (Nat × ByteArray) :=
    [(8315, UInt256.toByteArray (EVM.Word.ofNat v.factory.toNat)),
     (8829, UInt256.toByteArray (EVM.Word.ofNat v.factory.toNat)),
     (10457, UInt256.toByteArray (EVM.Word.ofNat v.factory.toNat)),
     (2258, UInt256.toByteArray (EVM.Word.ofNat v.token0.toNat)),
     (4853, UInt256.toByteArray (EVM.Word.ofNat v.token0.toNat)),
     (6740, UInt256.toByteArray (EVM.Word.ofNat v.token0.toNat)),
     (7822, UInt256.toByteArray (EVM.Word.ofNat v.token0.toNat)),
     (9150, UInt256.toByteArray (EVM.Word.ofNat v.token0.toNat)),
     (15650, UInt256.toByteArray (EVM.Word.ofNat v.token0.toNat)),
     (4551, UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat)),
     (6789, UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat)),
     (7924, UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat)),
     (9284, UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat)),
     (10529, UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat)),
     (15979, UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat)),
     (3311, UInt256.toByteArray (EVM.wordOfInt v.fee)),
     (6603, UInt256.toByteArray (EVM.wordOfInt v.fee)),
     (6658, UInt256.toByteArray (EVM.wordOfInt v.fee)),
     (10565, UInt256.toByteArray (EVM.wordOfInt v.fee)),
     (3072, value)]
  let post : List (Nat × ByteArray) :=
    [(19402, value), (19452, value),
     (8174, UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick)),
     (19295, UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick)),
     (19350, UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick)),
     (11259, UInt256.toByteArray (EVM.Word.ofNat v.original.toNat))]
  have hpatch' : patchRuntime uniswapV3PoolBytecode (pre ++ (10493, value) :: post) =
      some code := by
    dsimp [pre, post, value]
    simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup,
      toByteArray_eq_toBytesBE] using hpatch
  have hpost : ∀ p ∈ post, 10493 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 10493 := by
    intro p hp
    dsimp [post] at hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hsize : value.size = 32 := by
    dsimp [value]
    exact toByteArray_size _
  exact patchRuntime_extract_patch hsize hpost hpatch'

theorem uniswapV3PoolTickSpacingConstDecode {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    decode code ⟨10492⟩ = some (.Push .PUSH32, some (EVM.wordOfInt v.tickSpacing, 32)) := by
  have hsize := uniswapV3PoolPatchedSize hpatch
  have hget : code.get? ({ val := 10492 } : UInt256).toNat =
      uniswapV3PoolBytecode.get? ({ val := 10492 } : UInt256).toNat := by
    change code.get? 10492 = uniswapV3PoolBytecode.get? 10492
    apply get?_eq_of_extract_one
    · rw [hsize]
      native_decide
    · native_decide
    · exact patchRuntime_extract_eq (start := 10492) (stop := 10493)
        (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
        (by omega) (by native_decide)
        (fun p hp => by
          simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
            List.lookup] at hp
          rcases hp with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl
          all_goals omega) hpatch
  have hextract : code.extract' ({ val := 10492 } : UInt256).toNat.succ
      (({ val := 10492 } : UInt256).toNat.succ + 32) =
      UInt256.toByteArray (EVM.wordOfInt v.tickSpacing) := by
    change code.extract' 10493 10525 = UInt256.toByteArray (EVM.wordOfInt v.tickSpacing)
    unfold ByteArray.extract'
    have hguard : (decide (10493 < 2 ^ 64) && decide (10525 < 2 ^ 64)) = true := by
      native_decide
    rw [if_pos hguard]
    exact uniswapV3PoolTickSpacingPatchWord hpatch
  have hgetSome : code.get? ({ val := 10492 } : UInt256).toNat = some 0x7f := by
    rw [hget]
    native_decide
  have hparse : (some (0x7f : UInt8) >>= parseInstr) = some (.Push .PUSH32) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray
        (code.extract' ({ val := 10492 } : UInt256).toNat.succ
          (({ val := 10492 } : UInt256).toNat.succ + 32)), 32)) =
    some (Operation.Push Operation.POp.PUSH32, some (EVM.wordOfInt v.tickSpacing, 32))
  rw [hextract, uInt256OfByteArray_eq, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem uniswapV3PoolTickSpacingGetterJumpdestDecode {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    decode code ⟨10491⟩ = some (.JUMPDEST, .none) := by
  refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨10491⟩) (byte := 0x5b)
    (op := .JUMPDEST) hpatch (by native_decide) ?_ (by native_decide)
    (by native_decide) (by native_decide)
  change ∀ p ∈ patches v, 10492 ≤ p.1 ∨ p.1 + 32 ≤ 10491
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

theorem uniswapV3PoolTickSpacingGetterDupDecode {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    decode code ⟨10525⟩ = some (.DUP2, .none) := by
  refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨10525⟩) (byte := 0x81)
    (op := .DUP2) hpatch (by native_decide) ?_ (by native_decide)
    (by native_decide) (by native_decide)
  change ∀ p ∈ patches v, 10526 ≤ p.1 ∨ p.1 + 32 ≤ 10525
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

theorem uniswapV3PoolTickSpacingGetterJumpDecode {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    decode code ⟨10526⟩ = some (.JUMP, .none) := by
  refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨10526⟩) (byte := 0x56)
    (op := .JUMP) hpatch (by native_decide) ?_ (by native_decide)
    (by native_decide) (by native_decide)
  change ∀ p ∈ patches v, 10527 ≤ p.1 ∨ p.1 + 32 ≤ 10526
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

theorem uniswapV3PoolTickSpacingEntryWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcGetterEntryWf code ⟨2009⟩ ⟨2017⟩ ⟨10491⟩ := by
  dsimp [solcGetterEntryWf]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide

theorem uniswapV3PoolTickSpacingGetterWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcConstGetterWf code ⟨10491⟩ (EVM.wordOfInt v.tickSpacing) 32 .PUSH32 := by
  dsimp [solcConstGetterWf]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact uniswapV3PoolTickSpacingGetterJumpdestDecode hpatch
  · native_decide
  · exact uniswapV3PoolTickSpacingConstDecode hpatch
  · exact uniswapV3PoolTickSpacingGetterDupDecode hpatch
  · exact uniswapV3PoolTickSpacingGetterJumpDecode hpatch

private def tickSpacingStSignextend (s : State) (v : UInt256) (t : List UInt256) : State :=
  { s with
      machineState.stack := v :: t,
      machineState.gasAvailable := s.machineState.gasAvailable.subNat 5
      machineState.pc := s.machineState.pc + ⟨1⟩
      machineState.execLength := s.machineState.execLength + 1 }

private theorem tickSpacingSignextendXstep {code : ByteArray} {s : State} {pc a b : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pc)
    (hdec : decode code pc = some (.SIGNEXTEND, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s =
      if s.machineState.gasAvailable.toNat < 5 then .error .OutOfGass
      else .ok (tickSpacingStSignextend s (UInt256.signextend a b) t, .none) := by
  have hdecS : decode s.executionEnv.code s.machineState.pc = some (.SIGNEXTEND, .none) := by
    rw [hcode, hpc]
    exact hdec
  have hstep := step_signextend s hdecS
  have hnoOverflow : ¬ 1024 ≤ t.length := by omega
  simpa [hcode, hstk, GasConstants.Glow, tickSpacingStSignextend, hnoOverflow] using hstep

private theorem tickSpacingRDSignextend {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SIGNEXTEND, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.signextend a b :: t) mem aw rdata acc
      (k + 1) (C + 5) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee,
      hworld⟩
  · exact Or.inl hoog
  · have st := tickSpacingSignextendXstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 5
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨tickSpacingStSignextend s (UInt256.signextend a b) t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega,
        by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [tickSpacingStSignextend]; exact hcode
      · simp only [tickSpacingStSignextend]; rw [hpc]
      · rfl
      · simp only [tickSpacingStSignextend]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [tickSpacingStSignextend]; exact hmem
      · simp only [tickSpacingStSignextend]; exact haw
      · simp only [tickSpacingStSignextend]; exact hrdata
      · simp only [tickSpacingStSignextend]; exact hacc
      · exact hee
      · exact hworld

@[reducible] def solcReturnInt24FromMemWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p3 = some (.DUP1, .none)
  ∧ decode code p4 = some (.MLOAD, .none)
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨2⟩, 1))
  ∧ decode code p7 = some (.SWAP3, .none)
  ∧ decode code p8 = some (.SWAP1, .none)
  ∧ decode code p9 = some (.SWAP3, .none)
  ∧ decode code p10 = some (.SIGNEXTEND, .none)
  ∧ decode code p11 = some (.DUP3, .none)
  ∧ decode code p12 = some (.MSTORE, .none)
  ∧ decode code p13 = some (.MLOAD, .none)
  ∧ decode code p14 = some (.SWAP1, .none)
  ∧ decode code p15 = some (.DUP2, .none)
  ∧ decode code p16 = some (.SWAP1, .none)
  ∧ decode code p17 = some (.SUB, .none)
  ∧ decode code p18 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p20 = some (.ADD, .none)
  ∧ decode code p21 = some (.SWAP1, .none)
  ∧ decode code p22 = some (.RETURN, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcReturnInt24FromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc val ret : UInt256} {R : List UInt256}
    {mem memout rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (val :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcReturnInt24FromMemWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout :
      (UInt256.toByteArray (UInt256.signextend ⟨2⟩ val)).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 :
      memout.readWithPadding 128 32 = UInt256.toByteArray (UInt256.signextend ⟨2⟩ val))
    (hov : R.length + 9 ≤ 1024) :
    RDret code g s0 acc (UInt256.toByteArray (UInt256.signextend ⟨2⟩ val)) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
      hd16, hd17, hd18, hd20, hd21, hd22⟩
  have rd1 := RD.jumpdest h hd0 (by simp only [List.length_cons]; omega)
  have rd3 := RD.push1 rd1 ⟨64⟩ hd1 (by simp only [List.length_cons]; omega)
  have rd4 := RD.dup1 rd3 hd3 (by simp only [List.length_cons]; omega)
  have rd5 := RD.mload 0 ⟨128⟩ (UInt256.ofNat 3) rd4 hd4 mem_cost hmload64
    (by decide) (by simp only [List.length_cons]; omega)
  have rd7 := RD.push1 rd5 ⟨2⟩ hd5 (by simp only [List.length_cons]; omega)
  have rd8 := RD.swap3 rd7 hd7 (by simp only [List.length_cons]; omega)
  have rd9 := RD.swap1 rd8 hd8 (by simp only [List.length_cons]; omega)
  have rd10 := RD.swap3 rd9 hd9 (by simp only [List.length_cons]; omega)
  have rd11 := tickSpacingRDSignextend rd10 hd10
    (by simp only [List.length_cons]; omega)
  have rd12pre := RD.dup3 rd11 hd11 (by simp only [List.length_cons]; omega)
  have rd13 := RD.mstore 6 memout (UInt256.ofNat 5) rd12pre hd12 mem_cost
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
      exact hmemout)
    (by decide) (by simp only [List.length_cons]; omega)
  have rd14 := RD.mload 0 ⟨128⟩ (UInt256.ofNat 5) rd13 hd13 mem_cost hmemoutLoad64
    (by decide) (by simp only [List.length_cons]; omega)
  have rd15 := RD.swap1 rd14 hd14 (by simp only [List.length_cons]; omega)
  have rd16 := RD.dup2 rd15 hd15 (by simp only [List.length_cons]; omega)
  have rd17 := RD.swap1 rd16 hd16 (by simp only [List.length_cons]; omega)
  have rd18 := RD.sub rd17 hd17 (by simp only [List.length_cons]; omega)
  have rd20 := RD.push1 rd18 ⟨32⟩ hd18 (by simp only [List.length_cons]; omega)
  have rd21 := RD.add rd20 hd20 (by simp only [List.length_cons]; omega)
  have rd22 := RD.swap1 rd21 hd21 (by simp only [List.length_cons]; omega)
  exact RD.ret 0 (UInt256.toByteArray (UInt256.signextend ⟨2⟩ val)) rd22 hd22 mem_cost
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
          from by decide]
      exact hread128)
    (by simp only [List.length_cons]; omega)

theorem RD.solcInt24ConstGetterExternal {code : ByteArray} {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel entry routine returnPc val : UInt256} {width : Nat}
    {op : Operation.POp}
    (hreach : ∃ k C, RD code I g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      entry [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcConstGetterWf code routine val width op)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnInt24FromMemWf code returnPc) :
    RDret code g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.signextend ⟨2⟩ val)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ := RD.solcConstGetter (val := val) (width := width)
    (op := op) (R := [sel]) rdRoutine hgetter hret
    (by simp only [List.length_singleton]; omega)
  exact RD.solcReturnInt24FromMem rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (UInt256.signextend ⟨2⟩ val))
    (solcReturnMem_read128 (UInt256.signextend ⟨2⟩ val))
    (by simp only [List.length_singleton]; omega)

theorem uniswapV3PoolTickSpacingReturnWf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcReturnInt24FromMemWf code ⟨2017⟩ := by
  dsimp [solcReturnInt24FromMemWf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide

theorem uniswapV3PoolTickSpacingReturnJumpDest {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨2017⟩ = true :=
  uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide)

theorem uniswapV3PoolTickSpacingEvm {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 20 == I.calldata.extract 0 4) = true) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.signextend ⟨2⟩ (EVM.wordOfInt v.tickSpacing))) := by
  have hreach := uniswapV3PoolTickSpacingReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  exact RD.solcInt24ConstGetterExternal
    (sel := solcSelectorWord I) (entry := ⟨2009⟩) (routine := ⟨10491⟩)
    (returnPc := ⟨2017⟩) (val := EVM.wordOfInt v.tickSpacing) (width := 32)
    (op := .PUSH32) hreach
    (uniswapV3PoolTickSpacingEntryWf hpatch)
    (uniswapV3PoolTickSpacingGetterWf hpatch)
    (uniswapV3PoolJumpDestPatched10491 hpatch)
    (uniswapV3PoolTickSpacingReturnJumpDest hpatch)
    (uniswapV3PoolTickSpacingReturnWf hpatch)

theorem uniswapV3PoolTickSpacingSourceBody {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (∅ : Store) (tickspacingTransition v).body
      (.returned { contract := contract v, locals := ∅ }
        (initState cA gh bl σ σ₀ g A I)
        (some [Value.int v.tickSpacing])) := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (∅ : Store)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [.intLit v.tickSpacing] ] _
  exact nonpayableIntLiteralBodyReturns (initState cA gh bl σ σ₀ g A I)
    (∅ : Store) v.tickSpacing hwv

theorem uniswapV3PoolTickSpacingBodyCore {v : PoolImmutables}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsel : (uniswapV3PoolSelBytes 20 == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch := uniswapV3PoolDispatch_tickSpacing (v := v) (cd := I.calldata) hsel
  have hdecode := uniswapV3PoolTickSpacingDecode (v := v) (I := I) hsz
  have hbody := uniswapV3PoolTickSpacingSourceBody (v := v) (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hwv
  have hrd := uniswapV3PoolTickSpacingEvm (v := v) (code := code) (cA := cA)
    (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel
  have hsign := signextend_two_wordOfInt_tickSpacing v.tickSpacing
    v.tickSpacing_ge v.tickSpacing_lt
  exact hrd.reEquivExecution hcode hdispatch hdecode hbody hAccounts
    (returnEquiv_of_encode (by
      simpa [hsign] using int24ReturnEncodingInt v.tickSpacing
        v.tickSpacing_ge v.tickSpacing_lt))

end Benchmarks.UniswapV3Pool

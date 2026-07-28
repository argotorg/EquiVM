import Benchmarks.UniswapV3Pool.InitializeGetTickSqrtRatioNonzero

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

private theorem sqrtRatioBitWord_eq_zero_iff_source
    (absW : UInt256) (abs : Int) (mask : Nat) (wmask : UInt256)
    (habsW : absW = EVM.wordOfInt abs)
    (habs0 : 0 ≤ abs) (habsLt : abs < (EVM.wordModulus : Int))
    (hmaskLt : mask < EVM.wordModulus) (hwmask : wmask.toNat = mask) :
    (UInt256.land absW wmask = ⟨0⟩) ↔
      getSqrtRatioSourceTickRatioStepBitInt abs (mask : Int) = 0 := by
  unfold getSqrtRatioSourceTickRatioStepBitInt
  have hto : (UInt256.land absW wmask).toNat = Nat.land abs.toNat mask := by
    rw [habsW, u256_land_toNat, wordOfInt_nonneg_toNat_lt_wordModulus _ habs0 habsLt,
      hwmask]
    have hlandLt : Nat.land abs.toNat mask < UInt256.size := by
      exact lt_of_le_of_lt (nat_land_le_right _ _) (by simpa [EVM.wordModulus] using hmaskLt)
    exact Nat.mod_eq_of_lt hlandLt
  constructor
  · intro hzero
    have hz := congrArg UInt256.toNat hzero
    simpa [hto] using hz
  · intro hzero
    have hzeroNat : Nat.land abs.toNat mask = 0 := by
      simpa using hzero
    apply u256_inj
    rw [hto, hzeroNat]
    rfl

private theorem sqrtRatioRatioMaskedWord_clean (ratio : UInt256)
    (hratio : ratio.toNat ≤ 2 ^ (128 : Nat)) :
    getSqrtRatioRatioMaskedWord ratio = ratio := by
  apply u256_inj
  unfold getSqrtRatioRatioMaskedWord getSqrtRatioUint136Mask
  rw [uland_toNat]
  rw [show (⟨87112285931760246646623899502532662132735⟩ : UInt256).toNat =
    2 ^ (136 : Nat) - 1 by native_decide]
  change Nat.land (2 ^ (136 : Nat) - 1) ratio.toNat = ratio.toNat
  rw [nat_land_comm]
  rw [nat_land_mask_eq_mod]
  have hlt136 : ratio.toNat < 2 ^ (136 : Nat) := by
    exact lt_of_le_of_lt hratio (by norm_num)
  rw [Nat.mod_eq_of_lt hlt136]

private theorem sqrtRatioMulShiftWord_eq_source
    (ratioW factorW : UInt256) (ratio : Int) (constant : Nat)
    (hratioW : ratioW = EVM.wordOfInt ratio)
    (hratio0 : 0 ≤ ratio) (hratioLe : ratio ≤ (2 ^ (128 : Nat) : Int))
    (hfactorNat : factorW.toNat = constant)
    (hfactorLt : constant < 2 ^ (128 : Nat)) :
    UInt256.shiftRight (UInt256.mul factorW ratioW) ⟨128⟩ =
      EVM.wordOfInt (((ratio * (constant : Int)).toNat / 2 ^ (128 : Nat) : Nat) : Int) := by
  apply u256_inj
  have hratioLtWord : ratio < (EVM.wordModulus : Int) := by
    norm_num [EVM.wordModulus, EVM.twoPow] at hratioLe ⊢
    omega
  have hratioNat : ratioW.toNat = ratio.toNat := by
    rw [hratioW, wordOfInt_nonneg_toNat_lt_wordModulus _ hratio0 hratioLtWord]
  have hratioNatLe : ratio.toNat ≤ 2 ^ (128 : Nat) := by
    simpa using Int.toNat_le_toNat hratioLe
  have hratioWLe : ratioW.toNat ≤ 2 ^ (128 : Nat) := by
    rw [hratioNat]
    exact hratioNatLe
  rw [u256_mul_shiftRight128_toNat_of_factor_lt_q128 factorW ratioW]
  · rw [hfactorNat, hratioNat, Nat.mul_comm]
    have hprodNat : (ratio * (constant : Int)).toNat = ratio.toNat * constant := by
      rw [Int.toNat_mul hratio0 (by exact_mod_cast Nat.zero_le constant)]
      simp
    rw [← hprodNat]
    have hquot0 : 0 ≤ (((ratio * (constant : Int)).toNat / 2 ^ (128 : Nat) : Nat) : Int) := by
      exact_mod_cast Nat.zero_le _
    have hprodLt : ratio.toNat * constant < EVM.wordModulus := by
      have hconstLe : constant ≤ 2 ^ (128 : Nat) - 1 := by omega
      have hmulLe : ratio.toNat * constant ≤ 2 ^ (128 : Nat) *
          (2 ^ (128 : Nat) - 1) := by
        exact Nat.mul_le_mul hratioNatLe hconstLe
      norm_num [EVM.wordModulus, EVM.twoPow] at hmulLe ⊢
      omega
    have hquotLt : (((ratio * (constant : Int)).toNat / 2 ^ (128 : Nat) : Nat) : Int) <
        (EVM.wordModulus : Int) := by
      have hle : (ratio * (constant : Int)).toNat / 2 ^ (128 : Nat) ≤
          ratio.toNat * constant := by
        rw [hprodNat]
        exact Nat.div_le_self _ _
      exact_mod_cast lt_of_le_of_lt hle hprodLt
    rw [wordOfInt_nonneg_toNat_lt_wordModulus _ hquot0 hquotLt]
    rw [Int.toNat_natCast]
  · rw [hfactorNat]
    exact hfactorLt
  · exact hratioWLe

private theorem sqrtRatioStepBranchWord_eq_source
    (absW ratioW factorW wmask : UInt256) (abs ratio : Int) (mask constant : Nat)
    (habsW : absW = EVM.wordOfInt abs)
    (habs0 : 0 ≤ abs) (habsLt : abs < (EVM.wordModulus : Int))
    (hratioW : ratioW = EVM.wordOfInt ratio)
    (hratio0 : 0 ≤ ratio) (hratioLe : ratio ≤ (2 ^ (128 : Nat) : Int))
    (hmaskLt : mask < EVM.wordModulus) (hwmask : wmask.toNat = mask)
    (hfactorNat : factorW.toNat = constant)
    (hfactorLt : constant < 2 ^ (128 : Nat)) :
    (if UInt256.land absW wmask = ⟨0⟩ then ratioW
      else UInt256.shiftRight (UInt256.mul factorW ratioW) ⟨128⟩) =
      EVM.wordOfInt (getSqrtRatioSourceTickRatioStepRatioInt abs ratio
        (mask : Int) (constant : Int)) := by
  have hbit := sqrtRatioBitWord_eq_zero_iff_source absW abs mask wmask habsW habs0 habsLt
    hmaskLt hwmask
  by_cases hsrc : getSqrtRatioSourceTickRatioStepBitInt abs (mask : Int) = 0
  · rw [if_pos (hbit.mpr hsrc)]
    unfold getSqrtRatioSourceTickRatioStepRatioInt
    rw [if_pos hsrc]
    exact hratioW
  · rw [if_neg (fun hzero => hsrc (hbit.mp hzero))]
    unfold getSqrtRatioSourceTickRatioStepRatioInt
    rw [if_neg hsrc]
    exact sqrtRatioMulShiftWord_eq_source ratioW factorW ratio constant hratioW hratio0 hratioLe
      hfactorNat hfactorLt

private theorem getSqrtRatioInitialBranchWord_tickHi_eq_source (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342)
    (hhiWord : getTickHiWord I = EVM.wordOfInt (getTickSourceTickHiInt I)) :
    getSqrtRatioInitialBranchWord (getSqrtRatioAbsTickBranchWord (getTickHiWord I)) =
      EVM.wordOfInt (getSqrtRatioSourceTickHiInitialRatioInt I) := by
  let absW := getSqrtRatioAbsTickBranchWord (getTickHiWord I)
  let abs := getSqrtRatioSourceTickHiAbsTickInt I
  have habsW : absW = EVM.wordOfInt abs := by
    dsimp [absW, abs]
    exact getSqrtRatioAbsTickBranchWord_tickHi_eq_source_abs I hlo hhi hhiWord
  have habs0 : 0 ≤ abs := by
    dsimp [abs]
    exact getSqrtRatioSourceTickHiAbsTickInt_nonneg I
  have habsLt : abs < (EVM.wordModulus : Int) := by
    dsimp [abs]
    exact getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I
      (getSqrtRatioSourceTickHiAbsTickInt_le_maxTick I hlo hhi)
  have hbit := sqrtRatioBitWord_eq_zero_iff_source absW abs 1 (⟨1⟩ : UInt256)
    habsW habs0 habsLt (by norm_num [EVM.wordModulus, EVM.twoPow]) (by native_decide)
  unfold getSqrtRatioInitialBranchWord getSqrtRatioBit1Word
    getSqrtRatioSourceTickHiInitialRatioInt getSqrtRatioSourceTickHiBit1Int
  by_cases hsrc : getSqrtRatioSourceTickRatioStepBitInt abs (1 : Int) = 0
  · rw [if_pos (hbit.mpr hsrc)]
    have hsrcI : getSqrtRatioSourceTickHiBit1Int I = 0 := by
      simpa [abs, getSqrtRatioSourceTickHiBit1Int,
        getSqrtRatioSourceTickRatioStepBitInt] using hsrc
    have hsrcRaw :
        ((getSqrtRatioSourceTickHiAbsTickInt I).toNat.land 1 : Int) = 0 := by
      simpa [getSqrtRatioSourceTickHiBit1Int] using hsrcI
    rw [if_pos hsrcRaw]
    native_decide
  · rw [if_neg (fun hzero => hsrc (hbit.mp hzero))]
    have hsrcI : getSqrtRatioSourceTickHiBit1Int I ≠ 0 := by
      intro hzero
      exact hsrc (by
        simpa [abs, getSqrtRatioSourceTickHiBit1Int,
          getSqrtRatioSourceTickRatioStepBitInt] using hzero)
    have hsrcRaw :
        ((getSqrtRatioSourceTickHiAbsTickInt I).toNat.land 1 : Int) ≠ 0 := by
      intro hzero
      exact hsrcI (by simpa [getSqrtRatioSourceTickHiBit1Int] using hzero)
    rw [if_neg hsrcRaw]
    native_decide

private theorem getSqrtRatioInitialBranchWord_le_q128 (absTick : UInt256) :
    (getSqrtRatioInitialBranchWord absTick).toNat ≤ 2 ^ (128 : Nat) := by
  unfold getSqrtRatioInitialBranchWord
  by_cases h : getSqrtRatioBit1Word absTick = ⟨0⟩
  · simp [h, getSqrtRatioInitialEvenWord]
    native_decide
  · simp [h, getSqrtRatioInitialOddWord]
    native_decide

private theorem getSqrtRatioAfterAllBitsWord_tickHi_eq_source (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342)
    (hhiWord : getTickHiWord I = EVM.wordOfInt (getTickSourceTickHiInt I)) :
    getSqrtRatioAfterAllBitsWord
        (getSqrtRatioAbsTickBranchWord (getTickHiWord I))
        (getSqrtRatioInitialBranchWord
          (getSqrtRatioAbsTickBranchWord (getTickHiWord I))) =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit524288Int I) := by
  let absW := getSqrtRatioAbsTickBranchWord (getTickHiWord I)
  let r0 := getSqrtRatioInitialBranchWord absW
  let r2 := getSqrtRatioAfterBit2BranchWord absW r0
  let r4 := getSqrtRatioAfterBit4BranchWord absW r2
  let r8 := getSqrtRatioAfterBit8BranchWord absW r4
  let r16 := getSqrtRatioAfterBit16BranchWord absW r8
  let r32 := getSqrtRatioAfterBit32BranchWord absW r16
  let r64 := getSqrtRatioAfterBit64BranchWord absW r32
  let r128 := getSqrtRatioAfterBit128BranchWord absW r64
  let r256 := getSqrtRatioAfterBit256BranchWord absW r128
  let r512 := getSqrtRatioAfterBit512BranchWord absW r256
  let r1024 := getSqrtRatioAfterBit1024BranchWord absW r512
  let r2048 := getSqrtRatioAfterBit2048BranchWord absW r1024
  let r4096 := getSqrtRatioAfterBit4096BranchWord absW r2048
  let r8192 := getSqrtRatioAfterBit8192BranchWord absW r4096
  let r16384 := getSqrtRatioAfterBit16384BranchWord absW r8192
  let r32768 := getSqrtRatioAfterBit32768BranchWord absW r16384
  let r65536 := getSqrtRatioAfterBit65536BranchWord absW r32768
  let r131072 := getSqrtRatioAfterBit131072BranchWord absW r65536
  let r262144 := getSqrtRatioAfterBit262144BranchWord absW r131072
  let r524288 := getSqrtRatioAfterBit524288BranchWord absW r262144
  have habsW : absW = EVM.wordOfInt (getSqrtRatioSourceTickHiAbsTickInt I) := by
    dsimp [absW]
    exact getSqrtRatioAbsTickBranchWord_tickHi_eq_source_abs I hlo hhi hhiWord
  have habs0 : 0 ≤ getSqrtRatioSourceTickHiAbsTickInt I :=
    getSqrtRatioSourceTickHiAbsTickInt_nonneg I
  have habsLt : getSqrtRatioSourceTickHiAbsTickInt I < (EVM.wordModulus : Int) :=
    getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I
      (getSqrtRatioSourceTickHiAbsTickInt_le_maxTick I hlo hhi)
  have hstage (ratioW factorW wmask : UInt256) (ratio : Int) (mask constant : Nat)
      (hratioW : ratioW = EVM.wordOfInt ratio)
      (hratio0 : 0 ≤ ratio) (hratioLe : ratio ≤ (2 ^ (128 : Nat) : Int))
      (hmaskLt : mask < EVM.wordModulus) (hwmask : wmask.toNat = mask)
      (hfactorNat : factorW.toNat = constant) (hfactorLt : constant < 2 ^ (128 : Nat)) :
      (if UInt256.land absW wmask = ⟨0⟩ then ratioW
        else UInt256.shiftRight (UInt256.mul factorW ratioW) ⟨128⟩) =
        EVM.wordOfInt (getSqrtRatioSourceTickRatioStepRatioInt
          (getSqrtRatioSourceTickHiAbsTickInt I) ratio (mask : Int) (constant : Int)) :=
    sqrtRatioStepBranchWord_eq_source absW ratioW factorW wmask
      (getSqrtRatioSourceTickHiAbsTickInt I) ratio mask constant
      habsW habs0 habsLt hratioW hratio0 hratioLe
      hmaskLt hwmask hfactorNat hfactorLt
  have hr0 : r0 = EVM.wordOfInt (getSqrtRatioSourceTickHiInitialRatioInt I) := by
    dsimp [r0, absW]
    exact getSqrtRatioInitialBranchWord_tickHi_eq_source I hlo hhi hhiWord
  have hr0m : getSqrtRatioRatioMaskedWord r0 =
      EVM.wordOfInt (getSqrtRatioSourceTickHiInitialRatioInt I) := by
    rw [sqrtRatioRatioMaskedWord_clean r0 (getSqrtRatioInitialBranchWord_le_q128 absW), hr0]
  have hr2 : r2 =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit2Int I) := by
    simpa [r2, getSqrtRatioAfterBit2BranchWord, getSqrtRatioAfterBit2Word,
      getSqrtRatioBit2Word, getSqrtRatioFactor2Word, getSqrtRatioSourceTickHiAfterBit2Int,
      getSqrtRatioSourceFactor2Int] using
      hstage (getSqrtRatioRatioMaskedWord r0) getSqrtRatioFactor2Word (⟨2⟩ : UInt256)
        (getSqrtRatioSourceTickHiInitialRatioInt I) 2
        340248342086729790484326174814286782778
        hr0m (getSqrtRatioSourceTickHiInitialRatioInt_nonneg I)
        (getSqrtRatioSourceTickHiInitialRatioInt_le_q128 I)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr4 : r4 =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit4Int I) := by
    simpa [r4, getSqrtRatioAfterBit4BranchWord, getSqrtRatioAfterBit4Word,
      getSqrtRatioBit4Word, getSqrtRatioFactor4Word, getSqrtRatioSourceTickHiAfterBit4Int,
      getSqrtRatioSourceFactor4Int] using
      hstage r2 getSqrtRatioFactor4Word
        (⟨4⟩ : UInt256) (getSqrtRatioSourceTickHiAfterBit2Int I) 4
        340214320654664324051920982716015181260
        hr2 (getSqrtRatioSourceTickHiAfterBit2Int_nonneg I)
        (getSqrtRatioSourceTickHiAfterBit2Int_le_q128 I)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr8 : r8 =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit8Int I) := by
    simpa [r8, getSqrtRatioAfterBit8BranchWord, getSqrtRatioAfterBit8Word,
      getSqrtRatioBit8Word, getSqrtRatioFactor8Word, getSqrtRatioSourceTickHiAfterBit8Int,
      getSqrtRatioSourceFactor8Int] using
      hstage r4 getSqrtRatioFactor8Word (⟨8⟩ : UInt256)
        (getSqrtRatioSourceTickHiAfterBit4Int I) 8
        340146287995602323631171512101879684304
        hr4 (getSqrtRatioSourceTickHiAfterBit4Int_nonneg I)
        (getSqrtRatioSourceTickHiAfterBit4Int_le_q128 I)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr16 : r16 =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit16Int I) := by
    simpa [r16, getSqrtRatioAfterBit16BranchWord, getSqrtRatioAfterBit16Word,
      getSqrtRatioBit16Word, getSqrtRatioFactor16Word,
      getSqrtRatioSourceTickHiAfterBit16Int, getSqrtRatioSourceFactor16Int] using
      hstage r8 getSqrtRatioFactor16Word (⟨16⟩ : UInt256)
        (getSqrtRatioSourceTickHiAfterBit8Int I) 16
        340010263488231146823593991679159461444
        hr8 (getSqrtRatioSourceTickHiAfterBit8Int_nonneg I)
        (getSqrtRatioSourceTickHiAfterBit8Int_le_q128 I)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr32 : r32 =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit32Int I) := by
    simpa [r32, getSqrtRatioAfterBit32BranchWord, getSqrtRatioAfterBit32Word,
      getSqrtRatioBit32Word, getSqrtRatioFactor32Word,
      getSqrtRatioSourceTickHiAfterBit32Int, getSqrtRatioSourceFactor32Int] using
      hstage r16 getSqrtRatioFactor32Word (⟨32⟩ : UInt256)
        (getSqrtRatioSourceTickHiAfterBit16Int I) 32
        339738377640345403697157401104375502016
        hr16 (getSqrtRatioSourceTickHiAfterBit16Int_nonneg I)
        (getSqrtRatioSourceTickHiAfterBit16Int_le_q128 I)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr64 : r64 =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit64Int I) := by
    simpa [r64, getSqrtRatioAfterBit64BranchWord, getSqrtRatioAfterBit64Word,
      getSqrtRatioBit64Word, getSqrtRatioFactor64Word,
      getSqrtRatioSourceTickHiAfterBit64Int, getSqrtRatioSourceFactor64Int] using
      hstage r32 getSqrtRatioFactor64Word (⟨64⟩ : UInt256)
        (getSqrtRatioSourceTickHiAfterBit32Int I) 64
        339195258003219555707034227454543997025
        hr32 (getSqrtRatioSourceTickHiAfterBit32Int_nonneg I)
        (getSqrtRatioSourceTickHiAfterBit32Int_le_q128 I)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr128 : r128 =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit128Int I) := by
    simpa [r128, getSqrtRatioAfterBit128BranchWord, getSqrtRatioAfterBit128Word,
      getSqrtRatioBit128Word, getSqrtRatioFactor128Word,
      getSqrtRatioSourceTickHiAfterBit128Int, getSqrtRatioSourceFactor128Int] using
      hstage r64 getSqrtRatioFactor128Word (⟨128⟩ : UInt256)
        (getSqrtRatioSourceTickHiAfterBit64Int I) 128
        338111622100601834656805679988414885971
        hr64 (getSqrtRatioSourceTickHiAfterBit64Int_nonneg I)
        (getSqrtRatioSourceTickHiAfterBit64Int_le_q128 I)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr256 : r256 =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit256Int I) := by
    simpa [r256, getSqrtRatioAfterBit256BranchWord, getSqrtRatioAfterBit256Word,
      getSqrtRatioBit256Word, getSqrtRatioFactor256Word,
      getSqrtRatioSourceTickHiAfterBit256Int, getSqrtRatioSourceFactor256Int] using
      hstage r128 getSqrtRatioFactor256Word (⟨256⟩ : UInt256)
        (getSqrtRatioSourceTickHiAfterBit128Int I) 256
        335954724994790223023589805789778977700
        hr128 (getSqrtRatioSourceTickHiAfterBit128Int_nonneg I)
        (getSqrtRatioSourceTickHiAfterBit128Int_le_q128 I)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr512 : r512 =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit512Int I) := by
    simpa [r512, getSqrtRatioAfterBit512BranchWord, getSqrtRatioAfterBit512Word,
      getSqrtRatioBit512Word, getSqrtRatioFactor512Word,
      getSqrtRatioSourceTickHiAfterBit512Int, getSqrtRatioSourceFactor512Int] using
      hstage r256 getSqrtRatioFactor512Word (⟨512⟩ : UInt256)
        (getSqrtRatioSourceTickHiAfterBit256Int I) 512
        331682121138379247127172139078559817300
        hr256 (getSqrtRatioSourceTickHiAfterBit256Int_nonneg I)
        (getSqrtRatioSourceTickHiAfterBit256Int_le_q128 I)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr1024 : r1024 =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit1024Int I) := by
    simpa [r1024, getSqrtRatioAfterBit1024BranchWord, getSqrtRatioAfterBit1024Word,
      getSqrtRatioBit1024Word, getSqrtRatioFactor1024Word,
      getSqrtRatioSourceTickHiAfterBit1024Int, getSqrtRatioSourceFactor1024Int] using
      hstage r512 getSqrtRatioFactor1024Word (⟨1024⟩ : UInt256)
        (getSqrtRatioSourceTickHiAfterBit512Int I) 1024
        323299236684853023288211250268160618739
        hr512 (getSqrtRatioSourceTickHiAfterBit512Int_nonneg I)
        (getSqrtRatioSourceTickHiAfterBit512Int_le_q128 I)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr2048 : r2048 =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit2048Int I) := by
    simpa [r2048, getSqrtRatioAfterBit2048BranchWord, getSqrtRatioAfterBit2048Word,
      getSqrtRatioBit2048Word, getSqrtRatioFactor2048Word,
      getSqrtRatioSourceTickHiAfterBit2048Int, getSqrtRatioSourceFactor2048Int] using
      hstage r1024 getSqrtRatioFactor2048Word (⟨2048⟩ : UInt256)
        (getSqrtRatioSourceTickHiAfterBit1024Int I) 2048
        307163716377032989948697243942600083929
        hr1024 (getSqrtRatioSourceTickHiAfterBit1024Int_nonneg I)
        (getSqrtRatioSourceTickHiAfterBit1024Int_le_q128 I)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr4096 : r4096 =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit4096Int I) := by
    simpa [r4096, getSqrtRatioAfterBit4096BranchWord, getSqrtRatioAfterBit4096Word,
      getSqrtRatioBit4096Word, getSqrtRatioFactor4096Word,
      getSqrtRatioSourceTickHiAfterBit4096Int, getSqrtRatioSourceFactor4096Int] using
      hstage r2048 getSqrtRatioFactor4096Word (⟨4096⟩ : UInt256)
        (getSqrtRatioSourceTickHiAfterBit2048Int I) 4096
        277268403626896220162999269216087595045
        hr2048 (getSqrtRatioSourceTickHiAfterBit2048Int_nonneg I)
        (getSqrtRatioSourceTickHiAfterBit2048Int_le_q128 I)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr8192 : r8192 =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit8192Int I) := by
    simpa [r8192, getSqrtRatioAfterBit8192BranchWord, getSqrtRatioAfterBit8192Word,
      getSqrtRatioBit8192Word, getSqrtRatioFactor8192Word,
      getSqrtRatioSourceTickHiAfterBit8192Int, getSqrtRatioSourceFactor8192Int] using
      hstage r4096 getSqrtRatioFactor8192Word (⟨8192⟩ : UInt256)
        (getSqrtRatioSourceTickHiAfterBit4096Int I) 8192
        225923453940442621947126027127485391333
        hr4096 (getSqrtRatioSourceTickHiAfterBit4096Int_nonneg I)
        (getSqrtRatioSourceTickHiAfterBit4096Int_le_q128 I)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr16384 : r16384 =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit16384Int I) := by
    simpa [r16384, getSqrtRatioAfterBit16384BranchWord, getSqrtRatioAfterBit16384Word,
      getSqrtRatioBit16384Word, getSqrtRatioFactor16384Word,
      getSqrtRatioSourceTickHiAfterBit16384Int, getSqrtRatioSourceFactor16384Int] using
      hstage r8192 getSqrtRatioFactor16384Word (⟨16384⟩ : UInt256)
        (getSqrtRatioSourceTickHiAfterBit8192Int I) 16384
        149997214084966997727330242082538205943
        hr8192 (getSqrtRatioSourceTickHiAfterBit8192Int_nonneg I)
        (getSqrtRatioSourceTickHiAfterBit8192Int_le_q128 I)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr32768 : r32768 =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit32768Int I) := by
    simpa [r32768, getSqrtRatioAfterBit32768BranchWord, getSqrtRatioAfterBit32768Word,
      getSqrtRatioBit32768Word, getSqrtRatioFactor32768Word,
      getSqrtRatioSourceTickHiAfterBit32768Int, getSqrtRatioSourceFactor32768Int] using
      hstage r16384 getSqrtRatioFactor32768Word (⟨32768⟩ : UInt256)
        (getSqrtRatioSourceTickHiAfterBit16384Int I) 32768
        66119101136024775622716233608466517926
        hr16384 (getSqrtRatioSourceTickHiAfterBit16384Int_nonneg I)
        (getSqrtRatioSourceTickHiAfterBit16384Int_le_q128 I)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr65536 : r65536 =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit65536Int I) := by
    simpa [r65536, getSqrtRatioAfterBit65536BranchWord, getSqrtRatioAfterBit65536Word,
      getSqrtRatioBit65536Word, getSqrtRatioFactor65536Word,
      getSqrtRatioSourceTickHiAfterBit65536Int, getSqrtRatioSourceFactor65536Int] using
      hstage r32768 getSqrtRatioFactor65536Word (⟨65536⟩ : UInt256)
        (getSqrtRatioSourceTickHiAfterBit32768Int I) 65536
        12847376061809297530290974190478138313
        hr32768 (getSqrtRatioSourceTickHiAfterBit32768Int_nonneg I)
        (getSqrtRatioSourceTickHiAfterBit32768Int_le_q128 I)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr131072 : r131072 =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit131072Int I) := by
    simpa [r131072, getSqrtRatioAfterBit131072BranchWord, getSqrtRatioAfterBit131072Word,
      getSqrtRatioBit131072Word, getSqrtRatioFactor131072Word,
      getSqrtRatioSourceTickHiAfterBit131072Int, getSqrtRatioSourceFactor131072Int] using
      hstage r65536 getSqrtRatioFactor131072Word (⟨131072⟩ : UInt256)
        (getSqrtRatioSourceTickHiAfterBit65536Int I) 131072
        485053260817066172746253684029974020
        hr65536 (getSqrtRatioSourceTickHiAfterBit65536Int_nonneg I)
        (getSqrtRatioSourceTickHiAfterBit65536Int_le_q128 I)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr262144 : r262144 =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit262144Int I) := by
    simpa [r262144, getSqrtRatioAfterBit262144BranchWord, getSqrtRatioAfterBit262144Word,
      getSqrtRatioBit262144Word, getSqrtRatioFactor262144Word,
      getSqrtRatioSourceTickHiAfterBit262144Int, getSqrtRatioSourceFactor262144Int] using
      hstage r131072 getSqrtRatioFactor262144Word (⟨262144⟩ : UInt256)
        (getSqrtRatioSourceTickHiAfterBit131072Int I) 262144
        691415978906521570653435304214168
        hr131072 (getSqrtRatioSourceTickHiAfterBit131072Int_nonneg I)
        (getSqrtRatioSourceTickHiAfterBit131072Int_le_q128 I)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr524288 : r524288 =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit524288Int I) := by
    simpa [r524288, getSqrtRatioAfterBit524288BranchWord, getSqrtRatioAfterBit524288Word,
      getSqrtRatioBit524288Word, getSqrtRatioFactor524288Word,
      getSqrtRatioSourceTickHiAfterBit524288Int, getSqrtRatioSourceFactor524288Int] using
      hstage r262144 getSqrtRatioFactor524288Word (⟨524288⟩ : UInt256)
        (getSqrtRatioSourceTickHiAfterBit262144Int I) 524288
        1404880482679654955896180642
        hr262144 (getSqrtRatioSourceTickHiAfterBit262144Int_nonneg I)
        (getSqrtRatioSourceTickHiAfterBit262144Int_le_q128 I)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simpa [getSqrtRatioAfterAllBitsWord, getSqrtRatioAfterLowBitsWord,
    getSqrtRatioAfterHighBitsWord, absW, r0, r2, r4, r8, r16, r32, r64, r128, r256,
    r512, r1024, r2048, r4096, r8192, r16384, r32768, r65536, r131072, r262144,
    r524288] using hr524288

private theorem sgt_wordOfInt_int24_zero (i : Int)
    (hge : -(2 ^ 23 : Int) ≤ i) (hlt : i < 2 ^ 23) :
    UInt256.sgt (EVM.wordOfInt i) ⟨0⟩ = if 0 < i then ⟨1⟩ else ⟨0⟩ := by
  by_cases hpos : 0 < i
  · rw [if_pos hpos]
    have h0 : 0 ≤ i := by omega
    rw [wordOfInt_nonneg i h0]
    apply sgt_lit_one (m := 0)
    · norm_num
    · unfold EVM.word EVM.uintN UInt256.toNat
      simp only
      rw [Nat.mod_eq_of_lt]
      · omega
      · exact lt_trans ((Int.toNat_lt h0).2 hlt) (by norm_num [EVM.twoPow])
    · unfold EVM.word EVM.uintN UInt256.toNat
      simp only
      rw [Nat.mod_eq_of_lt]
      · exact lt_trans ((Int.toNat_lt h0).2 hlt) (by norm_num)
      · exact lt_trans ((Int.toNat_lt h0).2 hlt) (by norm_num [EVM.twoPow])
  · rw [if_neg hpos]
    by_cases hneg : i < 0
    · have hto := wordOfInt_neg_toNat_lt_wordModulus i hneg (by
        have hle : i.natAbs ≤ EVM.twoPow 23 := by
          have habs : (i.natAbs : Int) = -i := Int.ofNat_natAbs_of_nonpos (by omega)
          norm_num [EVM.twoPow] at hge ⊢
          omega
        exact lt_of_le_of_lt hle (by native_decide : EVM.twoPow 23 < EVM.wordModulus))
      unfold UInt256.sgt UInt256.sgtBool UInt256.fromBool Bool.toUInt256
      rw [hto]
      have hhigh : UInt256.size - i.natAbs ≥ 2 ^ (255 : Nat) := by
        have hle : i.natAbs ≤ 2 ^ 23 := by
          have habs : (i.natAbs : Int) = -i := Int.ofNat_natAbs_of_nonpos (by omega)
          norm_num at hge ⊢
          omega
        have hposAbs : 0 < i.natAbs := Int.natAbs_pos.mpr (by omega)
        norm_num [UInt256.size] at hle ⊢
        omega
      rw [if_pos hhigh]
      change (if (if false then decide (EVM.wordOfInt i > (⟨0⟩ : UInt256)) else false) = true
          then UInt256.ofNat 1 else UInt256.ofNat 0) = (⟨0⟩ : UInt256)
      rfl
    · have hi0 : i = 0 := by omega
      rw [hi0]
      native_decide

private theorem maxUint_div_toNat_eq (ratio : Int)
    (hratio0 : 0 ≤ ratio) (hden : ratio ≠ 0) :
    (EVM.wordModulus - 1) / ratio.toNat =
      ((2 ^ (256 : Nat) - 1 : Int) / ratio).toNat := by
  have hratioPos : 0 < ratio := lt_of_le_of_ne hratio0 (Ne.symm hden)
  apply Int.ofNat.inj
  change (((EVM.wordModulus - 1) / ratio.toNat : Nat) : Int) =
    (((2 ^ (256 : Nat) - 1 : Int) / ratio).toNat : Int)
  rw [Int.natCast_ediv]
  have hdivNonneg : 0 ≤ ((2 ^ (256 : Nat) - 1 : Int) / ratio) := by
    exact Int.ediv_nonneg (by norm_num) (by omega)
  rw [Int.toNat_of_nonneg hdivNonneg]
  norm_num [EVM.wordModulus, EVM.twoPow]
  rw [max_eq_left hratio0]

private theorem int_toNat_div_pow32_eq (ratio : Int) (hratio0 : 0 ≤ ratio) :
    ratio.toNat / 2 ^ (32 : Nat) = (ratio / (2 ^ (32 : Nat) : Int)).toNat := by
  apply Int.ofNat.inj
  change ((ratio.toNat / 2 ^ (32 : Nat) : Nat) : Int) =
    ((ratio / (2 ^ (32 : Nat) : Int)).toNat : Int)
  rw [Int.natCast_ediv]
  have hdivNonneg : 0 ≤ ratio / (2 ^ (32 : Nat) : Int) := by
    exact Int.ediv_nonneg hratio0 (by norm_num)
  rw [Int.toNat_of_nonneg hdivNonneg]
  rw [Int.toNat_of_nonneg hratio0]
  norm_num

private theorem getSqrtRatioFinalRatioWord_tickHi_eq_source
    (I : ExecutionEnv) (ratioW : UInt256) (ratio : Int)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342)
    (hhiWord : getTickHiWord I = EVM.wordOfInt (getTickSourceTickHiInt I))
    (hratioW : ratioW = EVM.wordOfInt ratio)
    (hratio0 : 0 ≤ ratio) (hratioLe : ratio ≤ (2 ^ (128 : Nat) : Int))
    (hden : ratio ≠ 0) :
    getSqrtRatioFinalRatioWord (getTickHiWord I) ratioW =
      EVM.wordOfInt (getSqrtRatioSourceFinalRatioIntOf (getTickSourceTickHiInt I) ratio) := by
  have hb := getTickSourceTickHiInt_int24_bounds I hlo hhi
  have htickPos : getSqrtRatioTickPosWord (getTickHiWord I) =
      if 0 < getTickSourceTickHiInt I then ⟨1⟩ else ⟨0⟩ := by
    unfold getSqrtRatioTickPosWord getSqrtRatioTickInt24Word
    rw [hhiWord]
    rw [signextend_two_wordOfInt_tickSpacing (getTickSourceTickHiInt I) hb.1 hb.2]
    exact sgt_wordOfInt_int24_zero (getTickSourceTickHiInt I) hb.1 hb.2
  have hratioLtWord : ratio < (EVM.wordModulus : Int) := by
    norm_num [EVM.wordModulus, EVM.twoPow] at hratioLe ⊢
    omega
  by_cases hpos : 0 < getTickSourceTickHiInt I
  · unfold getSqrtRatioFinalRatioWord
    rw [htickPos, if_pos hpos]
    rw [if_neg (by native_decide : (⟨1⟩ : UInt256) ≠ (⟨0⟩ : UInt256))]
    unfold getSqrtRatioInvertedWord getSqrtRatioMaxUintWord
    apply u256_inj
    rw [udiv_toNat]
    have hratioNat : ratioW.toNat = ratio.toNat := by
      rw [hratioW, wordOfInt_nonneg_toNat_lt_wordModulus _ hratio0 hratioLtWord]
    rw [hratioNat]
    rw [show (UInt256.lnot (⟨0⟩ : UInt256)).toNat = EVM.wordModulus - 1 by
      native_decide]
    have hfinal0 : 0 ≤ getSqrtRatioSourceFinalRatioIntOf (getTickSourceTickHiInt I) ratio :=
      getSqrtRatioSourceFinalRatioIntOf_nonneg _ _ hratio0
    have hfinalLt : getSqrtRatioSourceFinalRatioIntOf (getTickSourceTickHiInt I) ratio <
        (EVM.wordModulus : Int) :=
      getSqrtRatioSourceFinalRatioIntOf_lt_wordModulus _ _ hratioLtWord
    rw [wordOfInt_nonneg_toNat_lt_wordModulus _ hfinal0 hfinalLt]
    unfold getSqrtRatioSourceFinalRatioIntOf
    rw [if_pos hpos]
    exact maxUint_div_toNat_eq ratio hratio0 hden
  · unfold getSqrtRatioFinalRatioWord
    rw [htickPos, if_neg hpos]
    rw [if_pos (by native_decide : (⟨0⟩ : UInt256) = (⟨0⟩ : UInt256))]
    unfold getSqrtRatioSourceFinalRatioIntOf
    rw [if_neg hpos]
    exact hratioW

private theorem getSqrtRatioReturnAddWord_toNat_zero
    (ratioW : UInt256) (n : Nat) (hn : ratioW.toNat = n)
    (hrem : n % 2 ^ (32 : Nat) = 0) :
    (getSqrtRatioReturnAddWord ratioW).toNat = 0 := by
  have hremToNat : (getSqrtRatioRemainderWord ratioW).toNat = n % 2 ^ (32 : Nat) := by
    unfold getSqrtRatioRemainderWord getSqrtRatioRoundBaseWord UInt256.mod
    rw [show ((⟨4294967296⟩ : UInt256).val == 0) = false by native_decide]
    change ratioW.toNat % 4294967296 = n % 2 ^ (32 : Nat)
    rw [hn]
    norm_num
  have hremWord : getSqrtRatioRemainderWord ratioW = ⟨0⟩ := by
    apply u256_inj
    rw [hremToNat, hrem]
    rfl
  unfold getSqrtRatioReturnAddWord getSqrtRatioRoundUpFlagWord
  rw [hremWord]
  native_decide

private theorem getSqrtRatioReturnAddWord_toNat_one
    (ratioW : UInt256) (n : Nat) (hn : ratioW.toNat = n)
    (hrem : n % 2 ^ (32 : Nat) ≠ 0) :
    (getSqrtRatioReturnAddWord ratioW).toNat = 1 := by
  have hremToNat : (getSqrtRatioRemainderWord ratioW).toNat = n % 2 ^ (32 : Nat) := by
    unfold getSqrtRatioRemainderWord getSqrtRatioRoundBaseWord UInt256.mod
    rw [show ((⟨4294967296⟩ : UInt256).val == 0) = false by native_decide]
    change ratioW.toNat % 4294967296 = n % 2 ^ (32 : Nat)
    rw [hn]
    norm_num
  have hremWord : getSqrtRatioRemainderWord ratioW ≠ ⟨0⟩ := by
    intro hzero
    have hz := congrArg UInt256.toNat hzero
    rw [hremToNat] at hz
    exact hrem hz
  unfold getSqrtRatioReturnAddWord getSqrtRatioRoundUpFlagWord
  by_cases hz : getSqrtRatioRemainderWord ratioW = ⟨0⟩
  · exact False.elim (hremWord hz)
  · have hisZero : UInt256.isZero (getSqrtRatioRemainderWord ratioW) = ⟨0⟩ := by
      unfold UInt256.isZero UInt256.eq0 UInt256.fromBool Bool.toUInt256
      simp [hz]
      rfl
    rw [hisZero]
    native_decide

private theorem getSqrtRatioReturnWord_eq_source
    (ratioW : UInt256) (ratio : Int)
    (hratioW : ratioW = EVM.wordOfInt ratio)
    (hratio0 : 0 ≤ ratio) (hratioLt : ratio < (EVM.wordModulus : Int)) :
    getSqrtRatioReturnWord ratioW = EVM.wordOfInt (getSqrtRatioSourceReturnIntOf ratio) := by
  apply u256_inj
  have hratioNat : ratioW.toNat = ratio.toNat := by
    rw [hratioW, wordOfInt_nonneg_toNat_lt_wordModulus _ hratio0 hratioLt]
  unfold getSqrtRatioReturnWord getSqrtRatioSourceReturnIntOf
  rw [uadd_toNat]
  unfold UInt256.shiftRight
  rw [if_neg (by decide : ¬ (⟨32⟩ : UInt256).val ≥ 256)]
  unfold UInt256.toNat
  rw [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow]
  change (ratioW.toNat / 2 ^ (32 : Nat) + (getSqrtRatioReturnAddWord ratioW).toNat) %
      UInt256.size =
    (EVM.wordOfInt
      (↑(ratio.toNat / 2 ^ (32 : Nat)) +
        if (Value.int (ratio % (2 ^ (32 : Nat) : Int)) == Value.int 0) = true then 0
        else 1)).toNat
  rw [hratioNat]
  have hsumLt0 : ratio.toNat / 2 ^ (32 : Nat) + 1 < EVM.wordModulus := by
    have hratioNatLt : ratio.toNat < EVM.wordModulus := (Int.toNat_lt hratio0).2 hratioLt
    have hratioLt256 : ratio.toNat < 2 ^ (256 : Nat) := by
      simpa [EVM.wordModulus, EVM.twoPow] using hratioNatLt
    have hdivLt : ratio.toNat / 2 ^ (32 : Nat) < 2 ^ (224 : Nat) := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ (32 : Nat))]
      simpa [Nat.pow_add] using hratioLt256
    exact lt_trans (Nat.succ_lt_succ hdivLt) (by norm_num [EVM.wordModulus, EVM.twoPow])
  by_cases hrem : ratio.toNat % 2 ^ (32 : Nat) = 0
  · have hmodInt : ratio % (2 ^ (32 : Nat) : Int) = 0 := by
      have hto : (ratio % (2 ^ (32 : Nat) : Int)).toNat = 0 := by
        rw [Int.toNat_emod hratio0 (by norm_num : 0 ≤ (2 ^ (32 : Nat) : Int))]
        exact hrem
      have hnonneg : 0 ≤ ratio % (2 ^ (32 : Nat) : Int) :=
        Int.emod_nonneg ratio (by norm_num)
      omega
    have hadd := getSqrtRatioReturnAddWord_toNat_zero ratioW ratio.toNat hratioNat hrem
    have hbeq : (Value.int (ratio % (2 ^ (32 : Nat) : Int)) == Value.int 0) = true := by
      rw [hmodInt]
      native_decide
    rw [hadd, hbeq]
    simp only [if_true, add_zero]
    have hbaseLt : ratio.toNat / 2 ^ (32 : Nat) < EVM.wordModulus := by
      exact lt_of_le_of_lt (Nat.div_le_self _ _) ((Int.toNat_lt hratio0).2 hratioLt)
    rw [Nat.mod_eq_of_lt]
    · rw [wordOfInt_nonneg_toNat_lt_wordModulus _
        (by positivity : 0 ≤ ((ratio.toNat / 2 ^ (32 : Nat) : Nat) : Int))
        (by exact_mod_cast hbaseLt)]
      rw [Int.toNat_natCast]
    · simpa [UInt256.size, EVM.wordModulus] using hbaseLt
  · have hmodIntNe : ratio % (2 ^ (32 : Nat) : Int) ≠ 0 := by
      intro hmod
      apply hrem
      have hto := congrArg Int.toNat hmod
      rw [Int.toNat_emod hratio0 (by norm_num : 0 ≤ (2 ^ (32 : Nat) : Int))] at hto
      simpa using hto
    have hadd := getSqrtRatioReturnAddWord_toNat_one ratioW ratio.toNat hratioNat hrem
    have hbeq : (Value.int (ratio % (2 ^ (32 : Nat) : Int)) == Value.int 0) = false := by
      cases h : (Value.int (ratio % (2 ^ (32 : Nat) : Int)) == Value.int 0) <;> simp_all
    rw [hadd, hbeq]
    simp only [Bool.false_eq_true, if_false]
    rw [Nat.mod_eq_of_lt]
    · rw [wordOfInt_nonneg_toNat_lt_wordModulus _
        (by positivity : 0 ≤ ((ratio.toNat / 2 ^ (32 : Nat) : Nat) + 1 : Int))
        (by exact_mod_cast hsumLt0)]
      norm_num
      rw [max_eq_left hratio0]
      change ratio.toNat / 2 ^ (32 : Nat) + 1 =
        (ratio / (2 ^ (32 : Nat) : Int) + 1).toNat
      have hdivNonneg : 0 ≤ ratio / (2 ^ (32 : Nat) : Int) := by
        exact Int.ediv_nonneg hratio0 (by norm_num)
      rw [Int.toNat_add hdivNonneg (by norm_num : 0 ≤ (1 : Int))]
      rw [int_toNat_div_pow32_eq ratio hratio0]
      norm_num
    · simpa [UInt256.size, EVM.wordModulus] using hsumLt0

private theorem getSqrtRatioSourceReturnIntOf_nonneg (ratio : Int) :
    0 ≤ getSqrtRatioSourceReturnIntOf ratio := by
  unfold getSqrtRatioSourceReturnIntOf
  split <;> positivity

private theorem getSqrtRatioSourceReturnIntOf_lt_wordModulus (ratio : Int)
    (hratio0 : 0 ≤ ratio) (hratioLt : ratio < (EVM.wordModulus : Int)) :
    getSqrtRatioSourceReturnIntOf ratio < (EVM.wordModulus : Int) := by
  unfold getSqrtRatioSourceReturnIntOf
  have hratioNatLt : ratio.toNat < EVM.wordModulus := (Int.toNat_lt hratio0).2 hratioLt
  have hle : ratio.toNat / 2 ^ (32 : Nat) ≤ ratio.toNat := Nat.div_le_self _ _
  split <;> norm_num [EVM.wordModulus, EVM.twoPow] at * <;> omega

private def sqrtRatioStepIntByNat (abs : Nat) (ratio : Int) (mask constant : Int) : Int :=
  if ((Nat.land abs mask.toNat : Nat) : Int) = 0 then ratio
  else ((ratio * constant).toNat / 2 ^ (128 : Nat) : Nat)

private def sqrtRatioAfterAllIntByNat (abs : Nat) : Int :=
  let r0 :=
    if ((Nat.land abs 1 : Nat) : Int) = 0 then (2 ^ (128 : Nat) : Int)
    else (340265354078544963557816517032075149313 : Int)
  let r2 := sqrtRatioStepIntByNat abs r0 2 340248342086729790484326174814286782778
  let r4 := sqrtRatioStepIntByNat abs r2 4 340214320654664324051920982716015181260
  let r8 := sqrtRatioStepIntByNat abs r4 8 340146287995602323631171512101879684304
  let r16 := sqrtRatioStepIntByNat abs r8 16 340010263488231146823593991679159461444
  let r32 := sqrtRatioStepIntByNat abs r16 32 339738377640345403697157401104375502016
  let r64 := sqrtRatioStepIntByNat abs r32 64 339195258003219555707034227454543997025
  let r128 := sqrtRatioStepIntByNat abs r64 128 338111622100601834656805679988414885971
  let r256 := sqrtRatioStepIntByNat abs r128 256 335954724994790223023589805789778977700
  let r512 := sqrtRatioStepIntByNat abs r256 512 331682121138379247127172139078559817300
  let r1024 := sqrtRatioStepIntByNat abs r512 1024 323299236684853023288211250268160618739
  let r2048 := sqrtRatioStepIntByNat abs r1024 2048 307163716377032989948697243942600083929
  let r4096 := sqrtRatioStepIntByNat abs r2048 4096 277268403626896220162999269216087595045
  let r8192 := sqrtRatioStepIntByNat abs r4096 8192 225923453940442621947126027127485391333
  let r16384 := sqrtRatioStepIntByNat abs r8192 16384 149997214084966997727330242082538205943
  let r32768 := sqrtRatioStepIntByNat abs r16384 32768 66119101136024775622716233608466517926
  let r65536 := sqrtRatioStepIntByNat abs r32768 65536 12847376061809297530290974190478138313
  let r131072 := sqrtRatioStepIntByNat abs r65536 131072 485053260817066172746253684029974020
  let r262144 := sqrtRatioStepIntByNat abs r131072 262144 691415978906521570653435304214168
  let r524288 := sqrtRatioStepIntByNat abs r262144 524288 1404880482679654955896180642
  r524288

private theorem getSqrtRatioSourceTickHiAfterBit524288Int_eq_reflected (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit524288Int I =
      sqrtRatioAfterAllIntByNat (getSqrtRatioSourceTickHiAbsTickInt I).toNat := by
  unfold getSqrtRatioSourceTickHiAfterBit524288Int getSqrtRatioSourceTickHiAfterBit262144Int
    getSqrtRatioSourceTickHiAfterBit131072Int getSqrtRatioSourceTickHiAfterBit65536Int
    getSqrtRatioSourceTickHiAfterBit32768Int getSqrtRatioSourceTickHiAfterBit16384Int
    getSqrtRatioSourceTickHiAfterBit8192Int getSqrtRatioSourceTickHiAfterBit4096Int
    getSqrtRatioSourceTickHiAfterBit2048Int getSqrtRatioSourceTickHiAfterBit1024Int
    getSqrtRatioSourceTickHiAfterBit512Int getSqrtRatioSourceTickHiAfterBit256Int
    getSqrtRatioSourceTickHiAfterBit128Int getSqrtRatioSourceTickHiAfterBit64Int
    getSqrtRatioSourceTickHiAfterBit32Int getSqrtRatioSourceTickHiAfterBit16Int
    getSqrtRatioSourceTickHiAfterBit8Int getSqrtRatioSourceTickHiAfterBit4Int
    getSqrtRatioSourceTickHiAfterBit2Int getSqrtRatioSourceTickHiInitialRatioInt
    getSqrtRatioSourceTickHiBit1Int getSqrtRatioSourceTickRatioStepRatioInt
    getSqrtRatioSourceTickRatioStepBitInt sqrtRatioAfterAllIntByNat sqrtRatioStepIntByNat
    getSqrtRatioSourceFactor2Int getSqrtRatioSourceFactor4Int getSqrtRatioSourceFactor8Int
    getSqrtRatioSourceFactor16Int getSqrtRatioSourceFactor32Int getSqrtRatioSourceFactor64Int
    getSqrtRatioSourceFactor128Int getSqrtRatioSourceFactor256Int getSqrtRatioSourceFactor512Int
    getSqrtRatioSourceFactor1024Int getSqrtRatioSourceFactor2048Int
    getSqrtRatioSourceFactor4096Int getSqrtRatioSourceFactor8192Int
    getSqrtRatioSourceFactor16384Int getSqrtRatioSourceFactor32768Int
    getSqrtRatioSourceFactor65536Int getSqrtRatioSourceFactor131072Int
    getSqrtRatioSourceFactor262144Int getSqrtRatioSourceFactor524288Int
  rfl

private theorem sqrtRatioAfterAllIntByNat_range_lower :
    ((List.range 887273).all fun n =>
      2 ^ (64 : Nat) < (sqrtRatioAfterAllIntByNat n).toNat) = true := by
  native_decide

private theorem sqrtRatioAfterAllIntByNat_lower_of_le_max (n : Nat) (hn : n ≤ 887272) :
    2 ^ (64 : Nat) < (sqrtRatioAfterAllIntByNat n).toNat := by
  have hnmem : n ∈ List.range 887273 := by
    rw [List.mem_range]
    omega
  have hdecide := List.all_eq_true.mp sqrtRatioAfterAllIntByNat_range_lower n hnmem
  exact of_decide_eq_true hdecide

private theorem getSqrtRatioSourceTickHiAfterBit524288Int_gt_q64 (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342) :
    (2 ^ (64 : Nat) : Int) < getSqrtRatioSourceTickHiAfterBit524288Int I := by
  rw [getSqrtRatioSourceTickHiAfterBit524288Int_eq_reflected I]
  have hnatLe : (getSqrtRatioSourceTickHiAbsTickInt I).toNat ≤ 887272 := by
    exact Int.toNat_le_toNat (getSqrtRatioSourceTickHiAbsTickInt_le_maxTick I hlo hhi)
  exact Int.lt_toNat.mp (sqrtRatioAfterAllIntByNat_lower_of_le_max _ hnatLe)

private theorem getSqrtRatioSourceFinalRatioIntOf_lt_return_bound
    (tick ratio : Int) (hratioLe : ratio ≤ (2 ^ (128 : Nat) : Int))
    (hratioGt : (2 ^ (64 : Nat) : Int) < ratio) :
    getSqrtRatioSourceFinalRatioIntOf tick ratio <
      (((2 ^ (160 : Nat) - 1) * 2 ^ (32 : Nat) : Nat) : Int) := by
  unfold getSqrtRatioSourceFinalRatioIntOf
  by_cases hpos : 0 < tick
  · rw [if_pos hpos]
    let bound : Int := (((2 ^ (160 : Nat) - 1) * 2 ^ (32 : Nat) : Nat) : Int)
    have hdenPos : 0 < ratio := lt_trans (by norm_num) hratioGt
    have hdenGe : ((2 ^ (64 : Nat) + 1 : Nat) : Int) ≤ ratio := by
      omega
    have hbase : (2 ^ (256 : Nat) - 1 : Int) <
        bound * ((2 ^ (64 : Nat) + 1 : Nat) : Int) := by
      native_decide
    have hmulLe : bound * ((2 ^ (64 : Nat) + 1 : Nat) : Int) ≤ bound * ratio := by
      exact Int.mul_le_mul_of_nonneg_left hdenGe (by dsimp [bound]; norm_num)
    exact Int.ediv_lt_of_lt_mul hdenPos (lt_of_lt_of_le hbase hmulLe)
  · rw [if_neg hpos]
    exact lt_of_le_of_lt hratioLe (by native_decide)

private theorem getSqrtRatioSourceTickHiFinalRatioInt_lt_return_bound (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342) :
    getSqrtRatioSourceTickHiFinalRatioInt I <
      (((2 ^ (160 : Nat) - 1) * 2 ^ (32 : Nat) : Nat) : Int) := by
  unfold getSqrtRatioSourceTickHiFinalRatioInt
  exact getSqrtRatioSourceFinalRatioIntOf_lt_return_bound
    (getTickSourceTickHiInt I)
    (getSqrtRatioSourceTickHiAfterBit524288Int I)
    (getSqrtRatioSourceTickHiAfterBit524288Int_le_q128 I)
    (getSqrtRatioSourceTickHiAfterBit524288Int_gt_q64 I hlo hhi)

private theorem getSqrtRatioSourceReturnIntOf_lt_twoPow160_of_ratio_lt_return_bound
    (ratio : Int) (hratio0 : 0 ≤ ratio)
    (hratioLt :
      ratio < (((2 ^ (160 : Nat) - 1) * 2 ^ (32 : Nat) : Nat) : Int)) :
    getSqrtRatioSourceReturnIntOf ratio < (2 ^ (160 : Nat) : Int) := by
  unfold getSqrtRatioSourceReturnIntOf
  have hratioNatLt : ratio.toNat < (2 ^ (160 : Nat) - 1) * 2 ^ (32 : Nat) := by
    exact (Int.toNat_lt hratio0).2 hratioLt
  have hdivLtPred : ratio.toNat / 2 ^ (32 : Nat) < 2 ^ (160 : Nat) - 1 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ (32 : Nat))]
    simpa using hratioNatLt
  by_cases hbeq : (Value.int (ratio % (2 ^ (32 : Nat) : Int)) == Value.int 0) = true
  · rw [if_pos hbeq]
    have hdivLt : ratio.toNat / 2 ^ (32 : Nat) < 2 ^ (160 : Nat) := by
      omega
    exact_mod_cast hdivLt
  · rw [if_neg hbeq]
    have hsuccLt : ratio.toNat / 2 ^ (32 : Nat) + 1 < 2 ^ (160 : Nat) := by
      omega
    exact_mod_cast hsuccLt

theorem getSqrtRatioSourceTickHiReturnValue_eq_word (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342) :
    getSqrtRatioSourceReturnValueOf (getSqrtRatioSourceTickHiFinalRatioInt I) =
      getTickSourceSqrtRatioAtTickHiValue I := by
  have hhiWord := getTickHiWord_eq_source_of_bounds I hlo hhi
  let absW := getSqrtRatioAbsTickBranchWord (getTickHiWord I)
  let r0 := getSqrtRatioInitialBranchWord absW
  let rAll := getSqrtRatioAfterAllBitsWord absW r0
  have hAll : rAll = EVM.wordOfInt (getSqrtRatioSourceTickHiAfterBit524288Int I) := by
    dsimp [rAll, r0, absW]
    exact getSqrtRatioAfterAllBitsWord_tickHi_eq_source I hlo hhi hhiWord
  have hFinal : getSqrtRatioFinalRatioWord (getTickHiWord I) rAll =
      EVM.wordOfInt (getSqrtRatioSourceTickHiFinalRatioInt I) := by
    simpa [getSqrtRatioSourceTickHiFinalRatioInt] using
      getSqrtRatioFinalRatioWord_tickHi_eq_source I rAll
        (getSqrtRatioSourceTickHiAfterBit524288Int I) hlo hhi hhiWord hAll
        (getSqrtRatioSourceTickHiAfterBit524288Int_nonneg I)
        (getSqrtRatioSourceTickHiAfterBit524288Int_le_q128 I)
        (getSqrtRatioSourceTickHiAfterBit524288Int_ne_zero I)
  have hfinal0 : 0 ≤ getSqrtRatioSourceTickHiFinalRatioInt I := by
    unfold getSqrtRatioSourceTickHiFinalRatioInt
    exact getSqrtRatioSourceFinalRatioIntOf_nonneg _ _
      (getSqrtRatioSourceTickHiAfterBit524288Int_nonneg I)
  have hratioLt : getSqrtRatioSourceTickHiAfterBit524288Int I < (EVM.wordModulus : Int) := by
    exact lt_of_le_of_lt (getSqrtRatioSourceTickHiAfterBit524288Int_le_q128 I)
      (by norm_num [EVM.wordModulus, EVM.twoPow])
  have hfinalLt : getSqrtRatioSourceTickHiFinalRatioInt I < (EVM.wordModulus : Int) := by
    unfold getSqrtRatioSourceTickHiFinalRatioInt
    exact getSqrtRatioSourceFinalRatioIntOf_lt_wordModulus _ _ hratioLt
  have hReturn := getSqrtRatioReturnWord_eq_source
    (getSqrtRatioFinalRatioWord (getTickHiWord I) rAll)
    (getSqrtRatioSourceTickHiFinalRatioInt I) hFinal hfinal0 hfinalLt
  have hReturnNat := congrArg UInt256.toNat hReturn
  rw [wordOfInt_nonneg_toNat_lt_wordModulus _
    (getSqrtRatioSourceReturnIntOf_nonneg (getSqrtRatioSourceTickHiFinalRatioInt I))
    (getSqrtRatioSourceReturnIntOf_lt_wordModulus (getSqrtRatioSourceTickHiFinalRatioInt I)
      hfinal0 hfinalLt)] at hReturnNat
  unfold getSqrtRatioSourceReturnValueOf getTickSourceSqrtRatioAtTickHiValue
  unfold getTickHiSqrtRatioWord getSqrtRatioAtTickResultWord getSqrtRatioTailReturnWord
  dsimp [absW, r0, rAll] at hReturnNat
  rw [hReturnNat]
  apply congrArg Value.int
  exact (Int.toNat_of_nonneg
    (getSqrtRatioSourceReturnIntOf_nonneg (getSqrtRatioSourceTickHiFinalRatioInt I))).symm

private theorem getTickHiSqrtRatioWord_toNat_lt_twoPow160 (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342) :
    (getTickHiSqrtRatioWord I).toNat < 2 ^ (160 : Nat) := by
  have hret := getSqrtRatioSourceTickHiReturnValue_eq_word I hlo hhi
  have hretInt :
      getSqrtRatioSourceReturnIntOf (getSqrtRatioSourceTickHiFinalRatioInt I) =
        Int.ofNat (getTickHiSqrtRatioWord I).toNat := by
    unfold getSqrtRatioSourceReturnValueOf getTickSourceSqrtRatioAtTickHiValue at hret
    exact Value.int.inj hret
  have hfinal0 : 0 ≤ getSqrtRatioSourceTickHiFinalRatioInt I := by
    unfold getSqrtRatioSourceTickHiFinalRatioInt
    exact getSqrtRatioSourceFinalRatioIntOf_nonneg _ _
      (getSqrtRatioSourceTickHiAfterBit524288Int_nonneg I)
  have hretLt :
      getSqrtRatioSourceReturnIntOf (getSqrtRatioSourceTickHiFinalRatioInt I) <
        (2 ^ (160 : Nat) : Int) := by
    exact getSqrtRatioSourceReturnIntOf_lt_twoPow160_of_ratio_lt_return_bound
      (getSqrtRatioSourceTickHiFinalRatioInt I) hfinal0
      (getSqrtRatioSourceTickHiFinalRatioInt_lt_return_bound I hlo hhi)
  rw [hretInt] at hretLt
  exact Int.ofNat_lt.mp hretLt

private theorem getTickHiSqrtRatioCleanWord_eq_self (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342) :
    getTickHiSqrtRatioCleanWord (getTickHiSqrtRatioWord I) = getTickHiSqrtRatioWord I := by
  unfold getTickHiSqrtRatioCleanWord
  rw [u256_land_comm]
  exact slot0Uint160Mask_clean (getTickHiSqrtRatioWord_toNat_lt_twoPow160 I hlo hhi)

theorem getTickSourceFinalValue_eq_initializeTickValue (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342) :
    getTickSourceFinalValue I = initializeTickValue I := by
  have hlowWord := getTickLowWord_eq_source_of_bounds I hlo hhi
  have hhiWord := getTickHiWord_eq_source_of_bounds I hlo hhi
  have hlowValue := getTickSourceTickLowValue_eq_wordToElem_of_word I hlo hhi hlowWord
  have hhiValue := getTickSourceTickHiValue_eq_wordToElem_of_word I hlo hhi hhiWord
  have hclean := getTickHiSqrtRatioCleanWord_eq_self I hlo hhi
  by_cases heq : getTickSourceTickLowInt I = getTickSourceTickHiInt I
  · have hsourceEq : getTickSourceTickLowValue I = getTickSourceTickHiValue I := by
      unfold getTickSourceTickLowValue getTickSourceTickHiValue
      rw [heq]
    have hsourceBeq :
        (getTickSourceTickLowValue I == getTickSourceTickHiValue I) = true := by
      simp [hsourceEq]
    have hwordEq := getTickLowEqHiWord_eq_one_of_source_eq I hlowWord hhiWord heq
    have hinit : initializeTickValue I = wordToElem (.int int24Int) (getTickLowWord I) := by
      unfold initializeTickValue getTickEstimatedWord
      rw [hwordEq]
      rw [if_neg (by native_decide : ¬ ((⟨1⟩ : UInt256) = (⟨0⟩ : UInt256)))]
    unfold getTickSourceFinalValue
    rw [hsourceBeq, hinit]
    exact hlowValue
  · have hsourceBeq :
        (getTickSourceTickLowValue I == getTickSourceTickHiValue I) = false := by
      unfold getTickSourceTickLowValue getTickSourceTickHiValue
      cases h : (Value.int (getTickSourceTickLowInt I) ==
          Value.int (getTickSourceTickHiInt I)) <;> simp_all
    have hwordEq := getTickLowEqHiWord_eq_zero_of_source_ne I hlo hhi hlowWord hhiWord heq
    unfold getTickSourceFinalValue
    rw [hsourceBeq]
    by_cases hle :
        Int.ofNat (getTickHiSqrtRatioWord I).toNat ≤
          Int.ofNat (initializeArgWord I).toNat
    · rw [if_pos hle]
      have hgt0 :
          UInt256.gt (getTickHiSqrtRatioCleanWord (getTickHiSqrtRatioWord I))
            (initializeArgWord I) = ⟨0⟩ := by
        rw [hclean]
        exact ugt_zero (Int.ofNat_le.mp hle)
      have hinit : initializeTickValue I = wordToElem (.int int24Int) (getTickHiWord I) := by
        unfold initializeTickValue getTickEstimatedWord getTickAfterHiSqrtRatioWord
          getTickHiSqrtRatioGtInputWord
        rw [hwordEq]
        rw [if_pos (by native_decide : (⟨0⟩ : UInt256) = (⟨0⟩ : UInt256))]
        rw [hgt0]
        rw [if_pos (by native_decide : (⟨0⟩ : UInt256) = (⟨0⟩ : UInt256))]
      rw [hinit]
      exact hhiValue
    · rw [if_neg hle]
      have hgt1 :
          UInt256.gt (getTickHiSqrtRatioCleanWord (getTickHiSqrtRatioWord I))
            (initializeArgWord I) = ⟨1⟩ := by
        rw [hclean]
        exact ugt_one (by
          have hnotNat :
              ¬ (getTickHiSqrtRatioWord I).toNat ≤ (initializeArgWord I).toNat := by
            intro hnat
            exact hle (Int.ofNat_le.mpr hnat)
          omega)
      have hinit : initializeTickValue I = wordToElem (.int int24Int) (getTickLowWord I) := by
        unfold initializeTickValue getTickEstimatedWord getTickAfterHiSqrtRatioWord
          getTickHiSqrtRatioGtInputWord
        rw [hwordEq]
        rw [if_pos (by native_decide : (⟨0⟩ : UInt256) = (⟨0⟩ : UInt256))]
        rw [hgt1]
        rw [if_neg (by native_decide : ¬ ((⟨1⟩ : UInt256) = (⟨0⟩ : UInt256)))]
      rw [hinit]
      exact hlowValue

end Benchmarks.UniswapV3Pool

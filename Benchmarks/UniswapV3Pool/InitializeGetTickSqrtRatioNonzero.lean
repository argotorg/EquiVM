import Benchmarks.UniswapV3Pool.InitializeGetTickLog2Bridge
import Benchmarks.UniswapV3Pool.InitializeSourceGetSqrtRatioHighBits
import Benchmarks.UniswapV3Pool.InitializeSourceStorageEquiv
import Benchmarks.UniswapV3Pool.TickSpacing

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

theorem u256_mul_shiftRight128_toNat_of_factor_lt_q128
    (factor ratio : UInt256)
    (hfactor : factor.toNat < 2 ^ (128 : Nat))
    (hratio : ratio.toNat ≤ 2 ^ (128 : Nat)) :
    (UInt256.shiftRight (UInt256.mul factor ratio) ⟨128⟩).toNat =
      factor.toNat * ratio.toNat / 2 ^ (128 : Nat) := by
  unfold UInt256.shiftRight UInt256.mul
  simp only [UInt256.toNat]
  rw [if_neg]
  · rw [Fin.shiftRight_val]
    rw [Fin.val_mul]
    rw [Nat.mod_eq_of_lt]
    · rw [Nat.shiftRight_eq_div_pow]
      norm_num [UInt256.size]
    · have hmul :
          factor.val.val * ratio.val.val < 2 ^ (128 : Nat) * 2 ^ (128 : Nat) := by
        exact Nat.mul_lt_mul_of_lt_of_le hfactor hratio (Nat.zero_lt_of_lt hfactor)
      have hpow : 2 ^ (128 : Nat) * 2 ^ (128 : Nat) = UInt256.size := by
        norm_num [UInt256.size]
      omega
  · decide

private theorem sqrtRatioStepWord_lb
    (factor ratio : UInt256) (factorNat lbIn lbOut : Nat)
    (hfactorNat : factor.toNat = factorNat)
    (hfactorLt : factorNat < 2 ^ (128 : Nat))
    (hratioLo : lbIn ≤ ratio.toNat)
    (hratioHi : ratio.toNat ≤ 2 ^ (128 : Nat))
    (hlb : lbOut ≤ factorNat * lbIn / 2 ^ (128 : Nat)) :
    lbOut ≤ (UInt256.shiftRight (UInt256.mul factor ratio) ⟨128⟩).toNat := by
  rw [u256_mul_shiftRight128_toNat_of_factor_lt_q128]
  · rw [hfactorNat]
    exact le_trans hlb (Nat.div_le_div_right (Nat.mul_le_mul_left factorNat hratioLo))
  · rw [hfactorNat]
    exact hfactorLt
  · exact hratioHi

private theorem sqrtRatioStepWord_le_q128
    (factor ratio : UInt256) (factorNat : Nat)
    (hfactorNat : factor.toNat = factorNat)
    (hfactorLt : factorNat < 2 ^ (128 : Nat))
    (hratioHi : ratio.toNat ≤ 2 ^ (128 : Nat)) :
    (UInt256.shiftRight (UInt256.mul factor ratio) ⟨128⟩).toNat ≤ 2 ^ (128 : Nat) := by
  rw [u256_mul_shiftRight128_toNat_of_factor_lt_q128]
  · rw [hfactorNat]
    apply Nat.div_le_of_le_mul
    exact Nat.mul_le_mul (Nat.le_of_lt hfactorLt) hratioHi
  · rw [hfactorNat]
    exact hfactorLt
  · exact hratioHi

private theorem getSqrtRatioInitialMaskedBranchWord_lb (absTick : UInt256) :
    340265354078544963557816517032075149313 ≤
      (getSqrtRatioRatioMaskedWord (getSqrtRatioInitialBranchWord absTick)).toNat := by
  unfold getSqrtRatioRatioMaskedWord getSqrtRatioInitialBranchWord
  by_cases h : getSqrtRatioBit1Word absTick = ⟨0⟩
  · simp [h, getSqrtRatioInitialEvenWord, getSqrtRatioUint136Mask]
    native_decide
  · simp [h, getSqrtRatioInitialOddWord, getSqrtRatioUint136Mask]
    native_decide

private theorem getSqrtRatioInitialMaskedBranchWord_le_q128 (absTick : UInt256) :
    (getSqrtRatioRatioMaskedWord (getSqrtRatioInitialBranchWord absTick)).toNat ≤
      2 ^ (128 : Nat) := by
  unfold getSqrtRatioRatioMaskedWord getSqrtRatioInitialBranchWord
  by_cases h : getSqrtRatioBit1Word absTick = ⟨0⟩
  · simp [h, getSqrtRatioInitialEvenWord, getSqrtRatioUint136Mask]
    native_decide
  · simp [h, getSqrtRatioInitialOddWord, getSqrtRatioUint136Mask]
    native_decide

private theorem sourceSqrtRatioStepInt_lb
    (absTick ratio mask constant : Int) (constantNat lbIn lbOut : Nat)
    (hconstantNat : constant.toNat = constantNat)
    (hconstant0 : 0 ≤ constant)
    (hratioLo : (lbIn : Int) ≤ ratio)
    (hlbKeep : lbOut ≤ lbIn)
    (hlbMul : lbOut ≤ constantNat * lbIn / 2 ^ (128 : Nat)) :
    (lbOut : Int) ≤
      getSqrtRatioSourceTickRatioStepRatioInt absTick ratio mask constant := by
  unfold getSqrtRatioSourceTickRatioStepRatioInt
  by_cases h : getSqrtRatioSourceTickRatioStepBitInt absTick mask = 0
  · rw [if_pos h]
    exact le_trans (by exact_mod_cast hlbKeep) hratioLo
  · rw [if_neg h]
    have hratio0 : 0 ≤ ratio := le_trans (by norm_num : (0 : Int) ≤ lbIn) hratioLo
    have hratioNat : lbIn ≤ ratio.toNat := by
      have htmp := Int.toNat_le_toNat hratioLo
      simpa using htmp
    have hprod : (ratio * constant).toNat = ratio.toNat * constantNat := by
      rw [Int.toNat_mul hratio0 hconstant0, hconstantNat]
    have hNat : lbOut ≤ (ratio * constant).toNat / 2 ^ (128 : Nat) := by
      rw [hprod, Nat.mul_comm]
      exact le_trans hlbMul
        (Nat.div_le_div_right (Nat.mul_le_mul_left constantNat hratioNat))
    exact_mod_cast hNat

private theorem getTickSourceRatioNat_ge_min_shift (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat) :
    4295128739 * 2 ^ (32 : Nat) ≤ getTickSourceRatioNat I := by
  unfold getTickSourceRatioNat
  rw [Nat.mod_eq_of_lt]
  · exact Nat.mul_le_mul_right _ hlo
  · have harg := initializeArgWord_toNat_lt_twoPow160 I
    have hmul := Nat.mul_lt_mul_of_pos_right harg (by norm_num : 0 < 2 ^ (32 : Nat))
    rw [← Nat.pow_add] at hmul
    norm_num at hmul ⊢
    exact lt_trans hmul (by norm_num [EVM.wordModulus, EVM.twoPow])

private theorem getTickSourceRatioNat_lt_max_shift (I : ExecutionEnv)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342) :
    getTickSourceRatioNat I <
      1461446703485210103287273052203988822378723970342 * 2 ^ (32 : Nat) := by
  unfold getTickSourceRatioNat
  rw [Nat.mod_eq_of_lt]
  · exact Nat.mul_lt_mul_of_pos_right hhi (by norm_num : 0 < 2 ^ (32 : Nat))
  · have harg := initializeArgWord_toNat_lt_twoPow160 I
    have hmul := Nat.mul_lt_mul_of_pos_right harg (by norm_num : 0 < 2 ^ (32 : Nat))
    rw [← Nat.pow_add] at hmul
    norm_num at hmul ⊢
    exact lt_trans hmul (by norm_num [EVM.wordModulus, EVM.twoPow])

private theorem getTickSourceMsbAfter0Nat_le_191 (I : ExecutionEnv)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342) :
    getTickSourceMsbAfter0Nat I ≤ 191 := by
  have hratioMax := getTickSourceRatioNat_lt_max_shift I hhi
  have hratioLt192 : getTickSourceRatioNat I < 2 ^ (192 : Nat) := by
    exact lt_trans hratioMax (by native_decide)
  unfold getTickSourceMsbAfter0Nat getTickSourceMsbAfter1Nat getTickSourceMsbAfter2Nat
    getTickSourceMsbAfter3Nat getTickSourceMsbAfter4Nat getTickSourceMsbAfter5Nat
    getTickSourceMsbAfter6Nat
  by_cases h7 : getTickSourceRatioGt7 I
  · have hf7 : getTickSourceMsbF7Nat I = 128 := by simp [getTickSourceMsbF7Nat, h7]
    have hr7lt : getTickSourceRAfterMsb7Nat I < 2 ^ (64 : Nat) := by
      unfold getTickSourceRAfterMsb7Nat
      rw [hf7]
      rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ (128 : Nat))]
      rw [← Nat.pow_add]
      norm_num
      exact hratioLt192
    have hf6 : getTickSourceMsbF6Nat I = 0 := by
      unfold getTickSourceMsbF6Nat getTickSourceRAfterMsb7Gt6
      rw [show decide (getTickSourceRAfterMsb7Nat I > 0xFFFFFFFFFFFFFFFF) = false by
        apply decide_eq_false
        norm_num at hr7lt ⊢
        omega]
      simp
    have h5 := getTickSourceMsbF5Nat_le_32 I
    have h4 := getTickSourceMsbF4Nat_le_16 I
    have h3 := getTickSourceMsbF3Nat_le_8 I
    have h2 := getTickSourceMsbF2Nat_le_4 I
    have h1 := getTickSourceMsbF1Nat_le_2 I
    have h0 := getTickSourceMsbF0Nat_le_1 I
    omega
  · have hf7 : getTickSourceMsbF7Nat I = 0 := by simp [getTickSourceMsbF7Nat, h7]
    have h6 := getTickSourceMsbF6Nat_le_64 I
    have h5 := getTickSourceMsbF5Nat_le_32 I
    have h4 := getTickSourceMsbF4Nat_le_16 I
    have h3 := getTickSourceMsbF3Nat_le_8 I
    have h2 := getTickSourceMsbF2Nat_le_4 I
    have h1 := getTickSourceMsbF1Nat_le_2 I
    have h0 := getTickSourceMsbF0Nat_le_1 I
    omega

private theorem getTickSourceMsbAfter0Nat_ge_64 (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat) :
    64 ≤ getTickSourceMsbAfter0Nat I := by
  have hratioMin := getTickSourceRatioNat_ge_min_shift I hlo
  have hratioGt64 : 2 ^ (64 : Nat) - 1 < getTickSourceRatioNat I := by
    exact lt_of_lt_of_le (by native_decide) hratioMin
  unfold getTickSourceMsbAfter0Nat getTickSourceMsbAfter1Nat getTickSourceMsbAfter2Nat
    getTickSourceMsbAfter3Nat getTickSourceMsbAfter4Nat getTickSourceMsbAfter5Nat
    getTickSourceMsbAfter6Nat
  by_cases h7 : getTickSourceRatioGt7 I
  · have hf7 : getTickSourceMsbF7Nat I = 128 := by simp [getTickSourceMsbF7Nat, h7]
    omega
  · have hf7 : getTickSourceMsbF7Nat I = 0 := by simp [getTickSourceMsbF7Nat, h7]
    have hr7 : getTickSourceRAfterMsb7Nat I = getTickSourceRatioNat I := by
      unfold getTickSourceRAfterMsb7Nat
      rw [hf7]
      simp
    have hf6 : getTickSourceMsbF6Nat I = 64 := by
      unfold getTickSourceMsbF6Nat getTickSourceRAfterMsb7Gt6
      rw [hr7]
      rw [show decide (getTickSourceRatioNat I > 0xFFFFFFFFFFFFFFFF) = true by
        apply decide_eq_true
        norm_num at hratioGt64 ⊢
        omega]
      simp
    omega

private theorem getTickSourceLog2After50Int_lower (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat) :
    -((64 : Int) * 2 ^ (64 : Nat)) ≤ getTickSourceLog2After50Int I := by
  have hmsb := getTickSourceMsbAfter0Nat_ge_64 I hlo
  have hf63 : 0 ≤ (getTickSourceLogF63Nat I : Int) * (2 ^ (63 : Nat) : Int) := by
    positivity
  unfold getTickSourceLog2After50Int getTickSourceLog2AfterStep
    getTickSourceLog2After51Int getTickSourceLog2After52Int getTickSourceLog2After53Int
    getTickSourceLog2After54Int getTickSourceLog2After55Int getTickSourceLog2After56Int
    getTickSourceLog2After57Int getTickSourceLog2After58Int getTickSourceLog2After59Int
    getTickSourceLog2After60Int getTickSourceLog2After61Int getTickSourceLog2After62Int
    getTickSourceLog2After63Int getTickSourceLog2BaseInt getTickSourceLogStepLog2AfterInt
  unfold getTickSourceLog2AfterStep getTickSourceLogStepLog2AfterInt
  omega

private theorem getTickSourceLog2After50Int_upper (I : ExecutionEnv)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342) :
    getTickSourceLog2After50Int I ≤ (64 : Int) * 2 ^ (64 : Nat) - 2 ^ (50 : Nat) := by
  have hmsb := getTickSourceMsbAfter0Nat_le_191 I hhi
  have hf63 := getTickSourceLogF63Nat_le_1 I
  have hf62 := getTickSourceLogF62Nat_le_1 I
  have hf61 := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter62Nat I)
    (getTickSourceLogRAfter62Nat_mul_self_lt_wordModulus I)
  have hf60 := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter61Nat I)
    (getTickSourceLogRAfter61Nat_mul_self_lt_wordModulus I)
  have hf59 := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter60Nat I)
    (getTickSourceLogRAfter60Nat_mul_self_lt_wordModulus I)
  have hf58 := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter59Nat I)
    (getTickSourceLogRAfter59Nat_mul_self_lt_wordModulus I)
  have hf57 := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter58Nat I)
    (getTickSourceLogRAfter58Nat_mul_self_lt_wordModulus I)
  have hf56 := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter57Nat I)
    (getTickSourceLogRAfter57Nat_mul_self_lt_wordModulus I)
  have hf55 := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter56Nat I)
    (getTickSourceLogRAfter56Nat_mul_self_lt_wordModulus I)
  have hf54 := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter55Nat I)
    (getTickSourceLogRAfter55Nat_mul_self_lt_wordModulus I)
  have hf53 := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter54Nat I)
    (getTickSourceLogRAfter54Nat_mul_self_lt_wordModulus I)
  have hf52 := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter53Nat I)
    (getTickSourceLogRAfter53Nat_mul_self_lt_wordModulus I)
  have hf51 := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter52Nat I)
    (getTickSourceLogRAfter52Nat_mul_self_lt_wordModulus I)
  have hf50 := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter51Nat I)
    (getTickSourceLogRAfter51Nat_mul_self_lt_wordModulus I)
  unfold getTickSourceLog2After50Int getTickSourceLog2AfterStep
    getTickSourceLog2After51Int getTickSourceLog2After52Int getTickSourceLog2After53Int
    getTickSourceLog2After54Int getTickSourceLog2After55Int getTickSourceLog2After56Int
    getTickSourceLog2After57Int getTickSourceLog2After58Int getTickSourceLog2After59Int
    getTickSourceLog2After60Int getTickSourceLog2After61Int getTickSourceLog2After62Int
    getTickSourceLog2After63Int getTickSourceLog2BaseInt getTickSourceLogStepLog2AfterInt
  unfold getTickSourceLog2AfterStep getTickSourceLogStepLog2AfterInt at *
  norm_num at *
  omega

theorem getSqrtRatioSourceTickHiAbsTickInt_le_maxTick (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342) :
    getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272 := by
  have hlo2 := getTickSourceLog2After50Int_lower I hlo
  have hhi2 := getTickSourceLog2After50Int_upper I hhi
  unfold getSqrtRatioSourceTickHiAbsTickInt getTickSourceTickHiInt
  unfold getTickSourceLogSqrt10001Int getTickSourceTickHiOffsetInt
    getTickSourceFixedPoint128Int getTickSourceLogSqrt10001MultiplierInt
  omega

theorem getTickSourceTickHiInt_int24_bounds (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342) :
    -(2 ^ 23 : Int) ≤ getTickSourceTickHiInt I ∧ getTickSourceTickHiInt I < 2 ^ 23 := by
  have habs := getSqrtRatioSourceTickHiAbsTickInt_le_maxTick I hlo hhi
  unfold getSqrtRatioSourceTickHiAbsTickInt at habs
  by_cases hneg : getTickSourceTickHiInt I < 0
  · rw [if_pos hneg] at habs
    constructor <;> omega
  · rw [if_neg hneg] at habs
    constructor <;> omega

theorem getTickSourceTickLowInt_int24_bounds (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342) :
    -(2 ^ 23 : Int) ≤ getTickSourceTickLowInt I ∧ getTickSourceTickLowInt I < 2 ^ 23 := by
  have hlo2 := getTickSourceLog2After50Int_lower I hlo
  have hhi2 := getTickSourceLog2After50Int_upper I hhi
  unfold getTickSourceTickLowInt getTickSourceLogSqrt10001Int
  unfold getTickSourceTickLowOffsetInt getTickSourceFixedPoint128Int
    getTickSourceLogSqrt10001MultiplierInt
  omega

theorem getTickSourceTickHiNumerator_int256_bounds (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342) :
    -(2 ^ 255 : Int) ≤ getTickSourceLogSqrt10001Int I + getTickSourceTickHiOffsetInt ∧
      getTickSourceLogSqrt10001Int I + getTickSourceTickHiOffsetInt < 2 ^ 255 := by
  have hlo2 := getTickSourceLog2After50Int_lower I hlo
  have hhi2 := getTickSourceLog2After50Int_upper I hhi
  unfold getTickSourceLogSqrt10001Int getTickSourceLogSqrt10001MultiplierInt
    getTickSourceTickHiOffsetInt
  omega

theorem getTickSourceTickLowNumerator_int256_bounds (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342) :
    -(2 ^ 255 : Int) ≤ getTickSourceLogSqrt10001Int I - getTickSourceTickLowOffsetInt ∧
      getTickSourceLogSqrt10001Int I - getTickSourceTickLowOffsetInt < 2 ^ 255 := by
  have hlo2 := getTickSourceLog2After50Int_lower I hlo
  have hhi2 := getTickSourceLog2After50Int_upper I hhi
  unfold getTickSourceLogSqrt10001Int getTickSourceLogSqrt10001MultiplierInt
    getTickSourceTickLowOffsetInt
  omega

private theorem getTickSourceLogSqrt10001Int_int256_bounds (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342) :
    -(2 ^ 255 : Int) ≤ getTickSourceLogSqrt10001Int I ∧
      getTickSourceLogSqrt10001Int I < 2 ^ 255 := by
  have hlo2 := getTickSourceLog2After50Int_lower I hlo
  have hhi2 := getTickSourceLog2After50Int_upper I hhi
  unfold getTickSourceLogSqrt10001Int getTickSourceLogSqrt10001MultiplierInt
  constructor <;> omega

private theorem nat_sub_mul_mod_eq_sub_mul {S n c : Nat}
    (hprod : n * c < S) (hprodPos : 0 < n * c) (hc : 0 < c) :
    ((S - n) * c) % S = S - n * c := by
  have hprodLe : n * c ≤ S := le_of_lt hprod
  have hcSucc : c = (c - 1) + 1 := by omega
  rw [Nat.sub_mul]
  have hdecomp : S * c - n * c = (S - n * c) + S * (c - 1) := by
    calc
      S * c - n * c = S * ((c - 1) + 1) - n * c := by rw [← hcSucc]
      _ = (S * (c - 1) + S * 1) - n * c := by rw [Nat.mul_add]
      _ = (S * (c - 1) + S) - n * c := by rw [Nat.mul_one]
      _ = S + S * (c - 1) - n * c := by rw [Nat.add_comm]
      _ = S - n * c + S * (c - 1) := by rw [Nat.sub_add_comm hprodLe]
      _ = (S - n * c) + S * (c - 1) := rfl
  rw [hdecomp, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (Nat.sub_lt (Nat.zero_lt_of_lt hprod) hprodPos)

private theorem int_natAbs_mul_nat_of_neg {x : Int} {c : Nat} (hx : x < 0) (hc : 0 < c) :
    (x * (c : Int)).natAbs = x.natAbs * c := by
  apply (Nat.cast_inj (R := Int)).mp
  have hxAbs : (x.natAbs : Int) = -x := Int.ofNat_natAbs_of_nonpos (by omega)
  have hprodNeg : x * (c : Int) < 0 := by
    have hcInt : (0 : Int) < c := by exact_mod_cast hc
    exact mul_neg_of_neg_of_pos hx hcInt
  have hprodAbs : ((x * (c : Int)).natAbs : Int) = -(x * (c : Int)) :=
    Int.ofNat_natAbs_of_nonpos (by omega)
  rw [hprodAbs, Nat.cast_mul, hxAbs]
  norm_num

private theorem getTickSourceLog2After50Int_natAbs_lt_wordModulus_of_lower (I : ExecutionEnv)
    (hlo2 : -((64 : Int) * 2 ^ (64 : Nat)) ≤ getTickSourceLog2After50Int I)
    (hneg : getTickSourceLog2After50Int I < 0) :
    (getTickSourceLog2After50Int I).natAbs < EVM.wordModulus := by
  have habs : ((getTickSourceLog2After50Int I).natAbs : Int) =
      -getTickSourceLog2After50Int I := Int.ofNat_natAbs_of_nonpos (by omega)
  norm_num [EVM.wordModulus, EVM.twoPow] at hlo2 ⊢
  omega

private theorem getTickSourceLog2After50Int_mul_const_natAbs_lt_wordModulus_of_lower
    (I : ExecutionEnv)
    (hlo2 : -((64 : Int) * 2 ^ (64 : Nat)) ≤ getTickSourceLog2After50Int I)
    (hneg : getTickSourceLog2After50Int I < 0) :
    (getTickSourceLog2After50Int I * (255738958999603826347141 : Int)).natAbs <
      EVM.wordModulus := by
  change (getTickSourceLog2After50Int I * ((255738958999603826347141 : Nat) : Int)).natAbs <
    EVM.wordModulus
  rw [int_natAbs_mul_nat_of_neg
    (x := getTickSourceLog2After50Int I) (c := 255738958999603826347141) hneg
    (by norm_num)]
  have habs : ((getTickSourceLog2After50Int I).natAbs : Int) =
      -getTickSourceLog2After50Int I := Int.ofNat_natAbs_of_nonpos (by omega)
  norm_num [EVM.wordModulus, EVM.twoPow] at hlo2 ⊢
  omega

private theorem getTickLogSqrt10001Word_eq_source_of_log2_bounds_nonneg (I : ExecutionEnv)
    (hlog2 : getTickLog2After50Word I = EVM.wordOfInt (getTickSourceLog2After50Int I))
    (hhi2 : getTickSourceLog2After50Int I ≤
      (64 : Int) * 2 ^ (64 : Nat) - 2 ^ (50 : Nat))
    (hnonneg : 0 ≤ getTickSourceLog2After50Int I) :
    getTickLogSqrt10001Word I = EVM.wordOfInt (getTickSourceLogSqrt10001Int I) := by
  apply u256_inj
  unfold getTickLogSqrt10001Word getTickSourceLogSqrt10001Int
    getTickSourceLogSqrt10001MultiplierInt
  rw [hlog2]
  rw [u256_mul_toNat]
  have hconst : getTickLogSqrt10001Multiplier.toNat = 255738958999603826347141 := by
    native_decide
  rw [hconst]
  have hlog2Lt : getTickSourceLog2After50Int I < EVM.wordModulus := by
    norm_num [EVM.wordModulus, EVM.twoPow] at hhi2 ⊢
    omega
  have hprod0 : 0 ≤ getTickSourceLog2After50Int I *
      (255738958999603826347141 : Int) := by
    exact mul_nonneg hnonneg (by norm_num)
  have hprodLt :
      getTickSourceLog2After50Int I * (255738958999603826347141 : Int) <
        EVM.wordModulus := by
    norm_num [EVM.wordModulus, EVM.twoPow] at hhi2 ⊢
    omega
  rw [wordOfInt_nonneg_toNat_lt_wordModulus _ hnonneg hlog2Lt]
  rw [wordOfInt_nonneg_toNat_lt_wordModulus _ hprod0 hprodLt]
  have hprodNatLt :
      (getTickSourceLog2After50Int I).toNat * 255738958999603826347141 <
        UInt256.size := by
    have hto : ((getTickSourceLog2After50Int I).toNat : Int) =
        getTickSourceLog2After50Int I := Int.toNat_of_nonneg hnonneg
    norm_num [UInt256.size] at hprodLt ⊢
    omega
  rw [Nat.mod_eq_of_lt hprodNatLt]
  have hto : ((getTickSourceLog2After50Int I).toNat : Int) =
      getTickSourceLog2After50Int I := Int.toNat_of_nonneg hnonneg
  omega

private theorem getTickLogSqrt10001Word_eq_source_of_log2_bounds_neg (I : ExecutionEnv)
    (hlog2 : getTickLog2After50Word I = EVM.wordOfInt (getTickSourceLog2After50Int I))
    (hlo2 : -((64 : Int) * 2 ^ (64 : Nat)) ≤ getTickSourceLog2After50Int I)
    (hneg : getTickSourceLog2After50Int I < 0) :
    getTickLogSqrt10001Word I = EVM.wordOfInt (getTickSourceLogSqrt10001Int I) := by
  apply u256_inj
  unfold getTickLogSqrt10001Word getTickSourceLogSqrt10001Int
    getTickSourceLogSqrt10001MultiplierInt
  rw [hlog2]
  rw [u256_mul_toNat]
  have hconst : getTickLogSqrt10001Multiplier.toNat = 255738958999603826347141 := by
    native_decide
  rw [hconst]
  have hlog2AbsLt : (getTickSourceLog2After50Int I).natAbs < EVM.wordModulus :=
    getTickSourceLog2After50Int_natAbs_lt_wordModulus_of_lower I hlo2 hneg
  have hprodNeg :
      getTickSourceLog2After50Int I * (255738958999603826347141 : Int) < 0 := by
    exact mul_neg_of_neg_of_pos hneg (by norm_num)
  have hprodAbs :
      (getTickSourceLog2After50Int I *
        (255738958999603826347141 : Int)).natAbs =
          (getTickSourceLog2After50Int I).natAbs * 255738958999603826347141 :=
    int_natAbs_mul_nat_of_neg hneg (by norm_num)
  have hprodAbsLt :
      (getTickSourceLog2After50Int I *
        (255738958999603826347141 : Int)).natAbs < EVM.wordModulus :=
    getTickSourceLog2After50Int_mul_const_natAbs_lt_wordModulus_of_lower I hlo2 hneg
  rw [wordOfInt_neg_toNat_lt_wordModulus _ hneg hlog2AbsLt]
  rw [wordOfInt_neg_toNat_lt_wordModulus _ hprodNeg hprodAbsLt]
  rw [hprodAbs]
  have hprodLtSize :
      (getTickSourceLog2After50Int I).natAbs * 255738958999603826347141 <
        UInt256.size := by
    rw [← hprodAbs]
    simpa [EVM.wordModulus, EVM.twoPow, UInt256.size] using hprodAbsLt
  have hmod :
      (UInt256.size - (getTickSourceLog2After50Int I).natAbs) *
          255738958999603826347141 % UInt256.size =
        UInt256.size -
          (getTickSourceLog2After50Int I).natAbs * 255738958999603826347141 := by
    have hprodPos :
        0 < (getTickSourceLog2After50Int I).natAbs * 255738958999603826347141 := by
      exact Nat.mul_pos (Int.natAbs_pos.mpr (ne_of_lt hneg)) (by norm_num)
    exact nat_sub_mul_mod_eq_sub_mul hprodLtSize hprodPos (by norm_num)
  exact hmod

private theorem getTickLogSqrt10001Word_eq_source_of_log2_bounds (I : ExecutionEnv)
    (hlog2 : getTickLog2After50Word I = EVM.wordOfInt (getTickSourceLog2After50Int I))
    (hlo2 : -((64 : Int) * 2 ^ (64 : Nat)) ≤ getTickSourceLog2After50Int I)
    (hhi2 : getTickSourceLog2After50Int I ≤
      (64 : Int) * 2 ^ (64 : Nat) - 2 ^ (50 : Nat)) :
    getTickLogSqrt10001Word I = EVM.wordOfInt (getTickSourceLogSqrt10001Int I) := by
  by_cases hnonneg : 0 ≤ getTickSourceLog2After50Int I
  · exact getTickLogSqrt10001Word_eq_source_of_log2_bounds_nonneg I hlog2 hhi2 hnonneg
  · have hneg : getTickSourceLog2After50Int I < 0 := by omega
    exact getTickLogSqrt10001Word_eq_source_of_log2_bounds_neg I hlog2 hlo2 hneg

private theorem getTickLogSqrt10001Word_eq_source_of_bounds (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342) :
    getTickLogSqrt10001Word I = EVM.wordOfInt (getTickSourceLogSqrt10001Int I) := by
  have hloMsb := getTickSourceMsbAfter0Nat_ge_64 I hlo
  have hhiMsb := getTickSourceMsbAfter0Nat_le_191 I hhi
  exact getTickLogSqrt10001Word_eq_source_of_log2_bounds I
    (getTickLog2After50Word_eq_source_of_msb_bounds I hloMsb hhiMsb)
    (getTickSourceLog2After50Int_lower I hlo)
    (getTickSourceLog2After50Int_upper I hhi)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
private theorem getTickHiBiasedWord_eq_source_of_log (I : ExecutionEnv)
    (hlog : getTickLogSqrt10001Word I = EVM.wordOfInt (getTickSourceLogSqrt10001Int I))
    (hlogGe : -(2 ^ 255 : Int) ≤ getTickSourceLogSqrt10001Int I)
    (hlogLt : getTickSourceLogSqrt10001Int I < 2 ^ 255)
    (hsumGe :
      -(2 ^ 255 : Int) ≤ getTickSourceLogSqrt10001Int I + getTickSourceTickHiOffsetInt)
    (hsumLt : getTickSourceLogSqrt10001Int I + getTickSourceTickHiOffsetInt < 2 ^ 255) :
    getTickHiBiasedWord I =
      EVM.wordOfInt (getTickSourceLogSqrt10001Int I + getTickSourceTickHiOffsetInt) := by
  apply u256_inj
  unfold getTickHiBiasedWord getTickSourceTickHiOffsetInt
  rw [hlog, uadd_toNat]
  have hoff : getTickHiOffsetWord.toNat = 291339464771989622907027621153398088495 := by
    native_decide
  rw [hoff]
  let l := getTickSourceLogSqrt10001Int I
  change ((EVM.wordOfInt l).toNat + 291339464771989622907027621153398088495) %
      UInt256.size =
    (EVM.wordOfInt (l + 291339464771989622907027621153398088495)).toNat
  have hlogAbsLt : l.natAbs < EVM.wordModulus := by
    by_cases hneg : l < 0
    · have habs : (l.natAbs : Int) = -l := Int.ofNat_natAbs_of_nonpos (by omega)
      norm_num [l, EVM.wordModulus, EVM.twoPow] at hlogGe ⊢
      omega
    · have hnonneg : 0 ≤ l := by omega
      have habs : (l.natAbs : Int) = l := Int.natAbs_of_nonneg hnonneg
      have hlt : (l.natAbs : Int) < EVM.wordModulus := by
        rw [habs]
        exact lt_trans hlogLt (by norm_num [EVM.wordModulus, EVM.twoPow])
      exact_mod_cast hlt
  have hsumAbsLt : (l + 291339464771989622907027621153398088495).natAbs <
      EVM.wordModulus := by
    by_cases hneg : l + 291339464771989622907027621153398088495 < 0
    · have habs :
          ((l + 291339464771989622907027621153398088495).natAbs : Int) =
            -(l + 291339464771989622907027621153398088495) :=
        Int.ofNat_natAbs_of_nonpos (by omega)
      norm_num [l, EVM.wordModulus, EVM.twoPow] at hsumGe ⊢
      omega
    · have hnonneg : 0 ≤ l + 291339464771989622907027621153398088495 := by omega
      have habs :
          ((l + 291339464771989622907027621153398088495).natAbs : Int) =
            l + 291339464771989622907027621153398088495 :=
        Int.natAbs_of_nonneg hnonneg
      have hlt :
          ((l + 291339464771989622907027621153398088495).natAbs : Int) <
            EVM.wordModulus := by
        rw [habs]
        exact lt_trans (by simpa [l, getTickSourceTickHiOffsetInt] using hsumLt)
          (by norm_num [EVM.wordModulus, EVM.twoPow])
      exact_mod_cast hlt
  by_cases hlogNonneg : 0 ≤ l
  · have hlogLtWord : l < EVM.wordModulus :=
      lt_trans hlogLt (by norm_num [EVM.wordModulus, EVM.twoPow])
    rw [wordOfInt_nonneg_toNat_lt_wordModulus l hlogNonneg hlogLtWord]
    have hsumNonneg : 0 ≤ l + 291339464771989622907027621153398088495 := by omega
    have hsumLtWord : l + 291339464771989622907027621153398088495 <
        EVM.wordModulus :=
      lt_trans (by simpa [l, getTickSourceTickHiOffsetInt] using hsumLt)
        (by norm_num [EVM.wordModulus, EVM.twoPow])
    rw [wordOfInt_nonneg_toNat_lt_wordModulus _ hsumNonneg hsumLtWord]
    have hsumNatLt : l.toNat + 291339464771989622907027621153398088495 <
        UInt256.size := by
      have hlto : (l.toNat : Int) = l := Int.toNat_of_nonneg hlogNonneg
      norm_num [UInt256.size] at hsumLtWord ⊢
      omega
    rw [Nat.mod_eq_of_lt hsumNatLt]
    have hlto : (l.toNat : Int) = l := Int.toNat_of_nonneg hlogNonneg
    omega
  · have hlogNeg : l < 0 := by omega
    rw [wordOfInt_neg_toNat_lt_wordModulus l hlogNeg hlogAbsLt]
    by_cases hsumNonneg : 0 ≤ l + 291339464771989622907027621153398088495
    · have hsumLtWord : l + 291339464771989622907027621153398088495 <
            EVM.wordModulus :=
          lt_trans (by simpa [l, getTickSourceTickHiOffsetInt] using hsumLt)
            (by norm_num [EVM.wordModulus, EVM.twoPow])
      rw [wordOfInt_nonneg_toNat_lt_wordModulus _ hsumNonneg hsumLtWord]
      have habs : (l.natAbs : Int) = -l := Int.ofNat_natAbs_of_nonpos (by omega)
      have hwrap :
          UInt256.size ≤
            UInt256.size - l.natAbs + 291339464771989622907027621153398088495 := by
        norm_num [UInt256.size] at habs hsumNonneg ⊢
        omega
      have hsumLt2 :
          UInt256.size - l.natAbs + 291339464771989622907027621153398088495 <
            2 * UInt256.size := by
        have habsLtSize : l.natAbs < UInt256.size := by
          simpa [EVM.wordModulus, EVM.twoPow, UInt256.size] using hlogAbsLt
        norm_num [UInt256.size]
        omega
      have hmod :
          (UInt256.size - l.natAbs + 291339464771989622907027621153398088495) %
              UInt256.size =
            UInt256.size - l.natAbs + 291339464771989622907027621153398088495 -
              UInt256.size := by
        rw [Nat.mod_eq_sub_mod hwrap]
        rw [Nat.mod_eq_of_lt]
        omega
      rw [hmod]
      have hto : ((l + 291339464771989622907027621153398088495).toNat : Int) =
          l + 291339464771989622907027621153398088495 :=
        Int.toNat_of_nonneg hsumNonneg
      have hlogAbsLe : l.natAbs ≤ UInt256.size := by
        exact le_of_lt
          (by simpa [EVM.wordModulus, EVM.twoPow, UInt256.size] using hlogAbsLt)
      apply (Nat.cast_inj (R := Int)).mp
      rw [Nat.cast_sub hwrap]
      rw [Nat.cast_add]
      rw [Nat.cast_sub hlogAbsLe]
      rw [hto]
      rw [habs]
      norm_num [UInt256.size]
      ring
    · have hsumNeg : l + 291339464771989622907027621153398088495 < 0 := by omega
      rw [wordOfInt_neg_toNat_lt_wordModulus _ hsumNeg hsumAbsLt]
      have habsLog : (l.natAbs : Int) = -l := Int.ofNat_natAbs_of_nonpos (by omega)
      have habsSum :
          ((l + 291339464771989622907027621153398088495).natAbs : Int) =
            -(l + 291339464771989622907027621153398088495) :=
        Int.ofNat_natAbs_of_nonpos (by omega)
      have hltNoWrap :
          UInt256.size - l.natAbs + 291339464771989622907027621153398088495 <
            UInt256.size := by
        norm_num [UInt256.size] at habsLog hsumNeg ⊢
        omega
      rw [Nat.mod_eq_of_lt hltNoWrap]
      have hlogAbsLe : l.natAbs ≤ UInt256.size := by
        exact le_of_lt
          (by simpa [EVM.wordModulus, EVM.twoPow, UInt256.size] using hlogAbsLt)
      have hsumAbsLe :
          (l + 291339464771989622907027621153398088495).natAbs ≤ UInt256.size :=
        le_of_lt (by simpa [EVM.wordModulus, EVM.twoPow, UInt256.size] using hsumAbsLt)
      apply (Nat.cast_inj (R := Int)).mp
      rw [Nat.cast_add]
      rw [Nat.cast_sub hlogAbsLe]
      rw [Nat.cast_sub hsumAbsLe]
      rw [habsLog]
      rw [habsSum]
      norm_num [UInt256.size]
      ring

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
private theorem getTickLowBiasedWord_eq_source_of_log (I : ExecutionEnv)
    (hlog : getTickLogSqrt10001Word I = EVM.wordOfInt (getTickSourceLogSqrt10001Int I))
    (hlogGe : -(2 ^ 255 : Int) ≤ getTickSourceLogSqrt10001Int I)
    (hlogLt : getTickSourceLogSqrt10001Int I < 2 ^ 255)
    (hdiffGe :
      -(2 ^ 255 : Int) ≤ getTickSourceLogSqrt10001Int I - getTickSourceTickLowOffsetInt)
    (hdiffLt : getTickSourceLogSqrt10001Int I - getTickSourceTickLowOffsetInt < 2 ^ 255) :
    getTickLowBiasedWord I =
      EVM.wordOfInt (getTickSourceLogSqrt10001Int I - getTickSourceTickLowOffsetInt) := by
  apply u256_inj
  unfold getTickLowBiasedWord getTickSourceTickLowOffsetInt
  rw [hlog, uadd_toNat]
  have hoff : (UInt256.lnot getTickLowOffsetWord).toNat =
      UInt256.size - 3402992956809132418596140100660247210 := by
    native_decide
  rw [hoff]
  let l := getTickSourceLogSqrt10001Int I
  let off : Nat := 3402992956809132418596140100660247210
  change ((EVM.wordOfInt l).toNat + (UInt256.size - off)) % UInt256.size =
    (EVM.wordOfInt (l - (off : Int))).toNat
  have hlogAbsLt : l.natAbs < EVM.wordModulus := by
    by_cases hneg : l < 0
    · have habs : (l.natAbs : Int) = -l := Int.ofNat_natAbs_of_nonpos (by omega)
      norm_num [l, EVM.wordModulus, EVM.twoPow] at hlogGe ⊢
      omega
    · have hnonneg : 0 ≤ l := by omega
      have habs : (l.natAbs : Int) = l := Int.natAbs_of_nonneg hnonneg
      have hlt : (l.natAbs : Int) < EVM.wordModulus := by
        rw [habs]
        exact lt_trans hlogLt (by norm_num [EVM.wordModulus, EVM.twoPow])
      exact_mod_cast hlt
  have hdiffAbsLt : (l - (off : Int)).natAbs < EVM.wordModulus := by
    by_cases hneg : l - (off : Int) < 0
    · have habs : ((l - (off : Int)).natAbs : Int) = -(l - (off : Int)) :=
        Int.ofNat_natAbs_of_nonpos (by omega)
      norm_num [l, off, EVM.wordModulus, EVM.twoPow] at hdiffGe ⊢
      omega
    · have hnonneg : 0 ≤ l - (off : Int) := by omega
      have habs : ((l - (off : Int)).natAbs : Int) = l - (off : Int) :=
        Int.natAbs_of_nonneg hnonneg
      have hlt : ((l - (off : Int)).natAbs : Int) < EVM.wordModulus := by
        rw [habs]
        exact lt_trans (by simpa [l, off, getTickSourceTickLowOffsetInt] using hdiffLt)
          (by norm_num [EVM.wordModulus, EVM.twoPow])
      exact_mod_cast hlt
  by_cases hlogNonneg : 0 ≤ l
  · have hlogLtWord : l < EVM.wordModulus :=
      lt_trans hlogLt (by norm_num [EVM.wordModulus, EVM.twoPow])
    rw [wordOfInt_nonneg_toNat_lt_wordModulus l hlogNonneg hlogLtWord]
    by_cases hdiffNonneg : 0 ≤ l - (off : Int)
    · have hdiffLtWord : l - (off : Int) < EVM.wordModulus :=
        lt_trans (by simpa [l, off, getTickSourceTickLowOffsetInt] using hdiffLt)
          (by norm_num [EVM.wordModulus, EVM.twoPow])
      rw [wordOfInt_nonneg_toNat_lt_wordModulus _ hdiffNonneg hdiffLtWord]
      have hwrap : UInt256.size ≤ l.toNat + (UInt256.size - off) := by
        have hlto : (l.toNat : Int) = l := Int.toNat_of_nonneg hlogNonneg
        norm_num [off, UInt256.size] at hdiffNonneg hlto ⊢
        omega
      have hlt2 : l.toNat + (UInt256.size - off) < 2 * UInt256.size := by
        have hlogNatLt : l.toNat < UInt256.size := by
          exact (Int.toNat_lt hlogNonneg).2
            (by simpa [EVM.wordModulus, EVM.twoPow, UInt256.size] using hlogLtWord)
        norm_num [off]
        omega
      rw [Nat.mod_eq_sub_mod hwrap]
      rw [Nat.mod_eq_of_lt]
      ·
        have hlto : (l.toNat : Int) = l := Int.toNat_of_nonneg hlogNonneg
        have hto : ((l - (off : Int)).toNat : Int) = l - (off : Int) :=
          Int.toNat_of_nonneg hdiffNonneg
        apply (Nat.cast_inj (R := Int)).mp
        rw [Nat.cast_sub hwrap]
        rw [Nat.cast_add]
        rw [hlto]
        rw [hto]
        norm_num [off, UInt256.size]
        ring
      · omega
    · have hdiffNeg : l - (off : Int) < 0 := by omega
      rw [wordOfInt_neg_toNat_lt_wordModulus _ hdiffNeg hdiffAbsLt]
      have hltNoWrap : l.toNat + (UInt256.size - off) < UInt256.size := by
        have hlto : (l.toNat : Int) = l := Int.toNat_of_nonneg hlogNonneg
        norm_num [off, UInt256.size] at hdiffNeg hlto ⊢
        omega
      rw [Nat.mod_eq_of_lt hltNoWrap]
      have hlto : (l.toNat : Int) = l := Int.toNat_of_nonneg hlogNonneg
      have habsDiff : (((l - (off : Int)).natAbs) : Int) = -(l - (off : Int)) :=
        Int.ofNat_natAbs_of_nonpos (by omega)
      have hdiffAbsLe : (l - (off : Int)).natAbs ≤ UInt256.size := by
        exact le_of_lt
          (by simpa [EVM.wordModulus, EVM.twoPow, UInt256.size] using hdiffAbsLt)
      apply (Nat.cast_inj (R := Int)).mp
      rw [Nat.cast_add]
      rw [hlto]
      rw [Nat.cast_sub hdiffAbsLe]
      rw [habsDiff]
      norm_num [off, UInt256.size]
      ring
  · have hlogNeg : l < 0 := by omega
    rw [wordOfInt_neg_toNat_lt_wordModulus l hlogNeg hlogAbsLt]
    have hdiffNeg : l - (off : Int) < 0 := by omega
    rw [wordOfInt_neg_toNat_lt_wordModulus _ hdiffNeg hdiffAbsLt]
    have habsLog : (l.natAbs : Int) = -l := Int.ofNat_natAbs_of_nonpos (by omega)
    have habsDiff : (((l - (off : Int)).natAbs) : Int) = -(l - (off : Int)) :=
      Int.ofNat_natAbs_of_nonpos (by omega)
    have hwrap : UInt256.size ≤ UInt256.size - l.natAbs + (UInt256.size - off) := by
      norm_num [off, UInt256.size]
      omega
    have hlt2 : UInt256.size - l.natAbs + (UInt256.size - off) < 2 * UInt256.size := by
      have hdiffAbsLtSize : (l - (off : Int)).natAbs < UInt256.size := by
        simpa [EVM.wordModulus, EVM.twoPow, UInt256.size] using hdiffAbsLt
      have hsumEq :
          UInt256.size - l.natAbs + (UInt256.size - off) =
            2 * UInt256.size - (l - (off : Int)).natAbs := by
          have hlogAbsLe : l.natAbs ≤ UInt256.size := by
            exact le_of_lt
              (by simpa [EVM.wordModulus, EVM.twoPow, UInt256.size] using hlogAbsLt)
          have hdiffAbsLe2 : (l - (off : Int)).natAbs ≤ 2 * UInt256.size := by
            omega
          apply (Nat.cast_inj (R := Int)).mp
          rw [Nat.cast_add]
          rw [Nat.cast_sub hlogAbsLe]
          rw [Nat.cast_sub hdiffAbsLe2]
          rw [habsLog]
          rw [habsDiff]
          norm_num [off, UInt256.size]
          ring
      rw [hsumEq]
      exact Nat.sub_lt (by norm_num [UInt256.size]) (Int.natAbs_pos.mpr (ne_of_lt hdiffNeg))
    rw [Nat.mod_eq_sub_mod hwrap]
    rw [Nat.mod_eq_of_lt]
    ·
        have hlogAbsLe : l.natAbs ≤ UInt256.size := by
          exact le_of_lt
            (by simpa [EVM.wordModulus, EVM.twoPow, UInt256.size] using hlogAbsLt)
        have hdiffAbsLe : (l - (off : Int)).natAbs ≤ UInt256.size := by
          exact le_of_lt
            (by simpa [EVM.wordModulus, EVM.twoPow, UInt256.size] using hdiffAbsLt)
        apply (Nat.cast_inj (R := Int)).mp
        rw [Nat.cast_sub hwrap]
        rw [Nat.cast_add]
        rw [Nat.cast_sub hlogAbsLe]
        rw [Nat.cast_sub hdiffAbsLe]
        rw [habsLog]
        rw [habsDiff]
        norm_num [off, UInt256.size]
        ring
    · omega

private theorem getTickHiWord_eq_source_of_biased (I : ExecutionEnv)
    (hbiased : getTickHiBiasedWord I =
      EVM.wordOfInt (getTickSourceLogSqrt10001Int I + getTickSourceTickHiOffsetInt))
    (hge : -(2 ^ 255 : Int) ≤ getTickSourceLogSqrt10001Int I + getTickSourceTickHiOffsetInt)
    (hlt : getTickSourceLogSqrt10001Int I + getTickSourceTickHiOffsetInt < 2 ^ 255) :
    getTickHiWord I = EVM.wordOfInt (getTickSourceTickHiInt I) := by
  unfold getTickHiWord
  rw [hbiased]
  unfold getTickSourceTickHiInt getTickSourceFixedPoint128Int
  exact sar128_wordOfInt
    (getTickSourceLogSqrt10001Int I + getTickSourceTickHiOffsetInt) hge hlt

private theorem getTickLowWord_eq_source_of_biased (I : ExecutionEnv)
    (hbiased : getTickLowBiasedWord I =
      EVM.wordOfInt (getTickSourceLogSqrt10001Int I - getTickSourceTickLowOffsetInt))
    (hge : -(2 ^ 255 : Int) ≤ getTickSourceLogSqrt10001Int I - getTickSourceTickLowOffsetInt)
    (hlt : getTickSourceLogSqrt10001Int I - getTickSourceTickLowOffsetInt < 2 ^ 255) :
    getTickLowWord I = EVM.wordOfInt (getTickSourceTickLowInt I) := by
  unfold getTickLowWord
  rw [hbiased]
  unfold getTickSourceTickLowInt getTickSourceFixedPoint128Int
  exact sar128_wordOfInt
    (getTickSourceLogSqrt10001Int I - getTickSourceTickLowOffsetInt) hge hlt

theorem getTickHiWord_eq_source_of_bounds (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342) :
    getTickHiWord I = EVM.wordOfInt (getTickSourceTickHiInt I) := by
  have hlog := getTickLogSqrt10001Word_eq_source_of_bounds I hlo hhi
  have hlogBounds := getTickSourceLogSqrt10001Int_int256_bounds I hlo hhi
  have hnumBounds := getTickSourceTickHiNumerator_int256_bounds I hlo hhi
  exact getTickHiWord_eq_source_of_biased I
    (getTickHiBiasedWord_eq_source_of_log I hlog hlogBounds.1 hlogBounds.2
      hnumBounds.1 hnumBounds.2)
    hnumBounds.1 hnumBounds.2

theorem getTickLowWord_eq_source_of_bounds (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342) :
    getTickLowWord I = EVM.wordOfInt (getTickSourceTickLowInt I) := by
  have hlog := getTickLogSqrt10001Word_eq_source_of_bounds I hlo hhi
  have hlogBounds := getTickSourceLogSqrt10001Int_int256_bounds I hlo hhi
  have hnumBounds := getTickSourceTickLowNumerator_int256_bounds I hlo hhi
  exact getTickLowWord_eq_source_of_biased I
    (getTickLowBiasedWord_eq_source_of_log I hlog hlogBounds.1 hlogBounds.2
      hnumBounds.1 hnumBounds.2)
    hnumBounds.1 hnumBounds.2

theorem getTickSourceTickLowValue_eq_wordToElem_of_word (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342)
    (hword : getTickLowWord I = EVM.wordOfInt (getTickSourceTickLowInt I)) :
    getTickSourceTickLowValue I = wordToElem (.int int24Int) (getTickLowWord I) := by
  rw [hword]
  unfold getTickSourceTickLowValue
  have hb := getTickSourceTickLowInt_int24_bounds I hlo hhi
  exact (wordToElem_int24_wordOfInt (getTickSourceTickLowInt I) hb.1 hb.2).symm

theorem getTickSourceTickHiValue_eq_wordToElem_of_word (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342)
    (hword : getTickHiWord I = EVM.wordOfInt (getTickSourceTickHiInt I)) :
    getTickSourceTickHiValue I = wordToElem (.int int24Int) (getTickHiWord I) := by
  rw [hword]
  unfold getTickSourceTickHiValue
  have hb := getTickSourceTickHiInt_int24_bounds I hlo hhi
  exact (wordToElem_int24_wordOfInt (getTickSourceTickHiInt I) hb.1 hb.2).symm

theorem getTickLowEqHiWord_eq_one_of_source_eq (I : ExecutionEnv)
    (hlowWord : getTickLowWord I = EVM.wordOfInt (getTickSourceTickLowInt I))
    (hhiWord : getTickHiWord I = EVM.wordOfInt (getTickSourceTickHiInt I))
    (heq : getTickSourceTickLowInt I = getTickSourceTickHiInt I) :
    getTickLowEqHiWord I = ⟨1⟩ := by
  have hwordEq : getTickLowInt24Word I = getTickHiInt24Word I := by
    unfold getTickLowInt24Word getTickHiInt24Word
    rw [hlowWord, hhiWord, heq]
  unfold getTickLowEqHiWord
  rw [hwordEq]
  exact u256_eq_refl _

theorem getTickLowEqHiWord_eq_zero_of_source_ne (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342)
    (hlowWord : getTickLowWord I = EVM.wordOfInt (getTickSourceTickLowInt I))
    (hhiWord : getTickHiWord I = EVM.wordOfInt (getTickSourceTickHiInt I))
    (hne : getTickSourceTickLowInt I ≠ getTickSourceTickHiInt I) :
    getTickLowEqHiWord I = ⟨0⟩ := by
  have hlowBounds := getTickSourceTickLowInt_int24_bounds I hlo hhi
  have hhiBounds := getTickSourceTickHiInt_int24_bounds I hlo hhi
  have hwordNe : getTickLowInt24Word I ≠ getTickHiInt24Word I := by
    intro hwordEq
    have hlowSign :
        getTickLowInt24Word I = EVM.wordOfInt (getTickSourceTickLowInt I) := by
      unfold getTickLowInt24Word
      rw [hlowWord]
      exact signextend_two_wordOfInt_tickSpacing (getTickSourceTickLowInt I)
        hlowBounds.1 hlowBounds.2
    have hhiSign :
        getTickHiInt24Word I = EVM.wordOfInt (getTickSourceTickHiInt I) := by
      unfold getTickHiInt24Word
      rw [hhiWord]
      exact signextend_two_wordOfInt_tickSpacing (getTickSourceTickHiInt I)
        hhiBounds.1 hhiBounds.2
    have hwordOfIntEq :
        EVM.wordOfInt (getTickSourceTickLowInt I) =
          EVM.wordOfInt (getTickSourceTickHiInt I) := by
      rw [← hlowSign, ← hhiSign]
      exact hwordEq
    exact hne (wordOfInt_int24_inj hlowBounds.1 hlowBounds.2 hhiBounds.1 hhiBounds.2
      hwordOfIntEq)
  unfold getTickLowEqHiWord
  exact u256_eq_of_ne hwordNe

theorem getSqrtRatioAbsTickBranchWord_tickHi_eq_source_abs (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342)
    (hhiWord : getTickHiWord I = EVM.wordOfInt (getTickSourceTickHiInt I)) :
    getSqrtRatioAbsTickBranchWord (getTickHiWord I) =
      EVM.wordOfInt (getSqrtRatioSourceTickHiAbsTickInt I) := by
  have hb := getTickSourceTickHiInt_int24_bounds I hlo hhi
  unfold getSqrtRatioAbsTickBranchWord getSqrtRatioTickNegWord getSqrtRatioTickInt24Word
    getSqrtRatioAbsTickNegWord
  rw [hhiWord]
  rw [signextend_two_wordOfInt_tickSpacing (getTickSourceTickHiInt I) hb.1 hb.2]
  rw [slt_wordOfInt_int24_zero (getTickSourceTickHiInt I) hb.1 hb.2]
  unfold getSqrtRatioSourceTickHiAbsTickInt
  by_cases hneg : getTickSourceTickHiInt I < 0
  · simp only [hneg, ↓reduceIte]
    rw [if_neg (by native_decide : ¬ ((⟨1⟩ : UInt256) = ⟨0⟩))]
    unfold getSqrtRatioTickInt24Word
    rw [signextend_two_wordOfInt_tickSpacing (getTickSourceTickHiInt I) hb.1 hb.2]
    rw [show 0 - getTickSourceTickHiInt I = -getTickSourceTickHiInt I by omega]
    exact zero_sub_wordOfInt_int24_neg (getTickSourceTickHiInt I) hneg hb.1
  · simp only [hneg, ↓reduceIte]

theorem getSqrtRatioAbsTickBranchWord_tickHi_toNat_le_max (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342)
    (hhiWord : getTickHiWord I = EVM.wordOfInt (getTickSourceTickHiInt I)) :
    (getSqrtRatioAbsTickBranchWord (getTickHiWord I)).toNat ≤ getSqrtRatioMaxTickWord.toNat := by
  have hb := getTickSourceTickHiInt_int24_bounds I hlo hhi
  have hrange := getSqrtRatioSourceTickHiAbsTickInt_le_maxTick I hlo hhi
  unfold getSqrtRatioAbsTickBranchWord getSqrtRatioTickNegWord getSqrtRatioTickInt24Word
    getSqrtRatioAbsTickNegWord
  rw [hhiWord]
  rw [signextend_two_wordOfInt_tickSpacing (getTickSourceTickHiInt I) hb.1 hb.2]
  rw [slt_wordOfInt_int24_zero (getTickSourceTickHiInt I) hb.1 hb.2]
  by_cases hneg : getTickSourceTickHiInt I < 0
  · simp only [hneg, ↓reduceIte]
    rw [if_neg (by native_decide : ¬ ((⟨1⟩ : UInt256) = ⟨0⟩))]
    unfold getSqrtRatioTickInt24Word
    rw [signextend_two_wordOfInt_tickSpacing (getTickSourceTickHiInt I) hb.1 hb.2]
    rw [zero_sub_wordOfInt_int24_neg_toNat (getTickSourceTickHiInt I) hneg hb.1]
    rw [show getSqrtRatioMaxTickWord.toNat = 887272 by native_decide]
    have hrange' : -getTickSourceTickHiInt I ≤ 887272 := by
      unfold getSqrtRatioSourceTickHiAbsTickInt at hrange
      rw [if_pos hneg] at hrange
      omega
    exact Int.toNat_le_toNat hrange'
  · simp only [hneg, ↓reduceIte]
    have hnonneg : 0 ≤ getTickSourceTickHiInt I := by omega
    have hrange' : getTickSourceTickHiInt I ≤ 887272 := by
      unfold getSqrtRatioSourceTickHiAbsTickInt at hrange
      rw [if_neg hneg] at hrange
      exact hrange
    rw [wordOfInt_nonneg_toNat_lt_wordModulus (getTickSourceTickHiInt I) hnonneg]
    · rw [show getSqrtRatioMaxTickWord.toNat = 887272 by native_decide]
      exact Int.toNat_le_toNat hrange'
    · exact lt_of_le_of_lt hrange' (by norm_num [EVM.wordModulus, EVM.twoPow])

theorem getSqrtRatioAbsTickInRangeWord_tickHi_ne_zero (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342)
    (hhiWord : getTickHiWord I = EVM.wordOfInt (getTickSourceTickHiInt I)) :
    getSqrtRatioAbsTickInRangeWord
        (getSqrtRatioAbsTickBranchWord (getTickHiWord I)) ≠ ⟨0⟩ := by
  unfold getSqrtRatioAbsTickInRangeWord
  have hgt0 :
      UInt256.gt (getSqrtRatioAbsTickBranchWord (getTickHiWord I))
        getSqrtRatioMaxTickWord = ⟨0⟩ := by
    exact ugt_zero (getSqrtRatioAbsTickBranchWord_tickHi_toNat_le_max I hlo hhi hhiWord)
  rw [hgt0]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide]
  intro h
  cases h

private theorem getSqrtRatioSourceTickHiInitialRatioInt_lb (I : ExecutionEnv) :
    (340265354078544963557816517032075149313 : Int) ≤
      getSqrtRatioSourceTickHiInitialRatioInt I := by
  unfold getSqrtRatioSourceTickHiInitialRatioInt
  by_cases h : getSqrtRatioSourceTickHiBit1Int I = 0
  · simp [h]
  · simp [h]

theorem getSqrtRatioSourceTickHiAfterBit524288Int_ne_zero (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit524288Int I ≠ 0 := by
  have hr0lo := getSqrtRatioSourceTickHiInitialRatioInt_lb I
  have hr2lo : (340231330945450418515964920540021147198 : Int) ≤
      getSqrtRatioSourceTickHiAfterBit2Int I := by
    simpa [getSqrtRatioSourceTickHiAfterBit2Int] using
      sourceSqrtRatioStepInt_lb
        (getSqrtRatioSourceTickHiAbsTickInt I)
        (getSqrtRatioSourceTickHiInitialRatioInt I)
        2
        getSqrtRatioSourceFactor2Int
        340248342086729790484326174814286782778
        340265354078544963557816517032075149313
        340231330945450418515964920540021147198
        (by native_decide)
        (by native_decide)
        hr0lo
        (by native_decide)
        (by native_decide)
  have hr4lo : (340163294884840501567246455576441303173 : Int) ≤
      getSqrtRatioSourceTickHiAfterBit4Int I := by
    simpa [getSqrtRatioSourceTickHiAfterBit4Int] using
      sourceSqrtRatioStepInt_lb
        (getSqrtRatioSourceTickHiAbsTickInt I)
        (getSqrtRatioSourceTickHiAfterBit2Int I)
        4
        getSqrtRatioSourceFactor4Int
        340214320654664324051920982716015181260
        340231330945450418515964920540021147198
        340163294884840501567246455576441303173
        (by native_decide)
        (by native_decide)
        hr2lo
        (by native_decide)
        (by native_decide)
  have hr8lo : (340027263576413978334042125129128142263 : Int) ≤
      getSqrtRatioSourceTickHiAfterBit8Int I := by
    simpa [getSqrtRatioSourceTickHiAfterBit8Int] using
      sourceSqrtRatioStepInt_lb
        (getSqrtRatioSourceTickHiAbsTickInt I)
        (getSqrtRatioSourceTickHiAfterBit4Int I)
        8
        getSqrtRatioSourceFactor8Int
        340146287995602323631171512101879684304
        340163294884840501567246455576441303173
        340027263576413978334042125129128142263
        (by native_decide)
        (by native_decide)
        hr4lo
        (by native_decide)
        (by native_decide)
  have hr16lo : (339755364134575681238502878529008278326 : Int) ≤
      getSqrtRatioSourceTickHiAfterBit16Int I := by
    simpa [getSqrtRatioSourceTickHiAfterBit16Int] using
      sourceSqrtRatioStepInt_lb
        (getSqrtRatioSourceTickHiAbsTickInt I)
        (getSqrtRatioSourceTickHiAfterBit8Int I)
        16
        getSqrtRatioSourceFactor16Int
        340010263488231146823593991679159461444
        340027263576413978334042125129128142263
        339755364134575681238502878529008278326
        (by native_decide)
        (by native_decide)
        hr8lo
        (by native_decide)
        (by native_decide)
  have hr32lo : (339212217342146842559531600927033253847 : Int) ≤
      getSqrtRatioSourceTickHiAfterBit32Int I := by
    simpa [getSqrtRatioSourceTickHiAfterBit32Int] using
      sourceSqrtRatioStepInt_lb
        (getSqrtRatioSourceTickHiAbsTickInt I)
        (getSqrtRatioSourceTickHiAfterBit16Int I)
        32
        getSqrtRatioSourceFactor32Int
        339738377640345403697157401104375502016
        339755364134575681238502878529008278326
        339212217342146842559531600927033253847
        (by native_decide)
        (by native_decide)
        hr16lo
        (by native_decide)
        (by native_decide)
  have hr64lo : (338128527259088467778511436198880488164 : Int) ≤
      getSqrtRatioSourceTickHiAfterBit64Int I := by
    simpa [getSqrtRatioSourceTickHiAfterBit64Int] using
      sourceSqrtRatioStepInt_lb
        (getSqrtRatioSourceTickHiAbsTickInt I)
        (getSqrtRatioSourceTickHiAfterBit32Int I)
        64
        getSqrtRatioSourceFactor64Int
        339195258003219555707034227454543997025
        339212217342146842559531600927033253847
        338128527259088467778511436198880488164
        (by native_decide)
        (by native_decide)
        hr32lo
        (by native_decide)
        (by native_decide)
  have hr128lo : (335971522311117552149334092109581418674 : Int) ≤
      getSqrtRatioSourceTickHiAfterBit128Int I := by
    simpa [getSqrtRatioSourceTickHiAfterBit128Int] using
      sourceSqrtRatioStepInt_lb
        (getSqrtRatioSourceTickHiAbsTickInt I)
        (getSqrtRatioSourceTickHiAfterBit64Int I)
        128
        getSqrtRatioSourceFactor128Int
        338111622100601834656805679988414885971
        338128527259088467778511436198880488164
        335971522311117552149334092109581418674
        (by native_decide)
        (by native_decide)
        hr64lo
        (by native_decide)
        (by native_decide)
  have hr256lo : (331698704829854243503582989311158516586 : Int) ≤
      getSqrtRatioSourceTickHiAfterBit256Int I := by
    simpa [getSqrtRatioSourceTickHiAfterBit256Int] using
      sourceSqrtRatioStepInt_lb
        (getSqrtRatioSourceTickHiAbsTickInt I)
        (getSqrtRatioSourceTickHiAfterBit128Int I)
        256
        getSqrtRatioSourceFactor256Int
        335954724994790223023589805789778977700
        335971522311117552149334092109581418674
        331698704829854243503582989311158516586
        (by native_decide)
        (by native_decide)
        hr128lo
        (by native_decide)
        (by native_decide)
  have hr512lo : (323315401242583425022802937239550140918 : Int) ≤
      getSqrtRatioSourceTickHiAfterBit512Int I := by
    simpa [getSqrtRatioSourceTickHiAfterBit512Int] using
      sourceSqrtRatioStepInt_lb
        (getSqrtRatioSourceTickHiAbsTickInt I)
        (getSqrtRatioSourceTickHiAfterBit256Int I)
        512
        getSqrtRatioSourceFactor512Int
        331682121138379247127172139078559817300
        331698704829854243503582989311158516586
        323315401242583425022802937239550140918
        (by native_decide)
        (by native_decide)
        hr256lo
        (by native_decide)
        (by native_decide)
  have hr1024lo : (307179074178916392659402722612948179612 : Int) ≤
      getSqrtRatioSourceTickHiAfterBit1024Int I := by
    simpa [getSqrtRatioSourceTickHiAfterBit1024Int] using
      sourceSqrtRatioStepInt_lb
        (getSqrtRatioSourceTickHiAbsTickInt I)
        (getSqrtRatioSourceTickHiAfterBit512Int I)
        1024
        getSqrtRatioSourceFactor1024Int
        323299236684853023288211250268160618739
        323315401242583425022802937239550140918
        307179074178916392659402722612948179612
        (by native_decide)
        (by native_decide)
        hr512lo
        (by native_decide)
        (by native_decide)
  have hr2048lo : (277282266700509388632609933215391170106 : Int) ≤
      getSqrtRatioSourceTickHiAfterBit2048Int I := by
    simpa [getSqrtRatioSourceTickHiAfterBit2048Int] using
      sourceSqrtRatioStepInt_lb
        (getSqrtRatioSourceTickHiAbsTickInt I)
        (getSqrtRatioSourceTickHiAfterBit1024Int I)
        2048
        getSqrtRatioSourceFactor2048Int
        307163716377032989948697243942600083929
        307179074178916392659402722612948179612
        277282266700509388632609933215391170106
        (by native_decide)
        (by native_decide)
        hr1024lo
        (by native_decide)
        (by native_decide)
  have hr4096lo : (225934749830749445986089663015556949343 : Int) ≤
      getSqrtRatioSourceTickHiAfterBit4096Int I := by
    simpa [getSqrtRatioSourceTickHiAfterBit4096Int] using
      sourceSqrtRatioStepInt_lb
        (getSqrtRatioSourceTickHiAbsTickInt I)
        (getSqrtRatioSourceTickHiAfterBit2048Int I)
        4096
        getSqrtRatioSourceFactor4096Int
        277268403626896220162999269216087595045
        277282266700509388632609933215391170106
        225934749830749445986089663015556949343
        (by native_decide)
        (by native_decide)
        hr2048lo
        (by native_decide)
        (by native_decide)
  have hr8192lo : (150004713758184102711002566140788444796 : Int) ≤
      getSqrtRatioSourceTickHiAfterBit8192Int I := by
    simpa [getSqrtRatioSourceTickHiAfterBit8192Int] using
      sourceSqrtRatioStepInt_lb
        (getSqrtRatioSourceTickHiAbsTickInt I)
        (getSqrtRatioSourceTickHiAfterBit4096Int I)
        8192
        getSqrtRatioSourceFactor8192Int
        225923453940442621947126027127485391333
        225934749830749445986089663015556949343
        150004713758184102711002566140788444796
        (by native_decide)
        (by native_decide)
        hr4096lo
        (by native_decide)
        (by native_decide)
  have hr16384lo : (66122407008436832627027740713496573148 : Int) ≤
      getSqrtRatioSourceTickHiAfterBit16384Int I := by
    simpa [getSqrtRatioSourceTickHiAfterBit16384Int] using
      sourceSqrtRatioStepInt_lb
        (getSqrtRatioSourceTickHiAbsTickInt I)
        (getSqrtRatioSourceTickHiAfterBit8192Int I)
        16384
        getSqrtRatioSourceFactor16384Int
        149997214084966997727330242082538205943
        150004713758184102711002566140788444796
        66122407008436832627027740713496573148
        (by native_decide)
        (by native_decide)
        hr8192lo
        (by native_decide)
        (by native_decide)
  have hr32768lo : (12848018414553970828728179856918040433 : Int) ≤
      getSqrtRatioSourceTickHiAfterBit32768Int I := by
    simpa [getSqrtRatioSourceTickHiAfterBit32768Int] using
      sourceSqrtRatioStepInt_lb
        (getSqrtRatioSourceTickHiAbsTickInt I)
        (getSqrtRatioSourceTickHiAfterBit16384Int I)
        32768
        getSqrtRatioSourceFactor32768Int
        66119101136024775622716233608466517926
        66122407008436832627027740713496573148
        12848018414553970828728179856918040433
        (by native_decide)
        (by native_decide)
        hr16384lo
        (by native_decide)
        (by native_decide)
  have hr65536lo : (485077512873820763967752669154895175 : Int) ≤
      getSqrtRatioSourceTickHiAfterBit65536Int I := by
    simpa [getSqrtRatioSourceTickHiAfterBit65536Int] using
      sourceSqrtRatioStepInt_lb
        (getSqrtRatioSourceTickHiAbsTickInt I)
        (getSqrtRatioSourceTickHiAfterBit32768Int I)
        65536
        getSqrtRatioSourceFactor65536Int
        12847376061809297530290974190478138313
        12848018414553970828728179856918040433
        485077512873820763967752669154895175
        (by native_decide)
        (by native_decide)
        hr32768lo
        (by native_decide)
        (by native_decide)
  have hr131072lo : (691450548841240133896843047535567 : Int) ≤
      getSqrtRatioSourceTickHiAfterBit131072Int I := by
    simpa [getSqrtRatioSourceTickHiAfterBit131072Int] using
      sourceSqrtRatioStepInt_lb
        (getSqrtRatioSourceTickHiAbsTickInt I)
        (getSqrtRatioSourceTickHiAfterBit65536Int I)
        131072
        getSqrtRatioSourceFactor131072Int
        485053260817066172746253684029974020
        485077512873820763967752669154895175
        691450548841240133896843047535567
        (by native_decide)
        (by native_decide)
        hr65536lo
        (by native_decide)
        (by native_decide)
  have hr262144lo : (1404950724947776134837143967 : Int) ≤
      getSqrtRatioSourceTickHiAfterBit262144Int I := by
    simpa [getSqrtRatioSourceTickHiAfterBit262144Int] using
      sourceSqrtRatioStepInt_lb
        (getSqrtRatioSourceTickHiAbsTickInt I)
        (getSqrtRatioSourceTickHiAfterBit131072Int I)
        262144
        getSqrtRatioSourceFactor262144Int
        691415978906521570653435304214168
        691450548841240133896843047535567
        1404950724947776134837143967
        (by native_decide)
        (by native_decide)
        hr131072lo
        (by native_decide)
        (by native_decide)
  have hr524288lo : (5800441176149320 : Int) ≤
      getSqrtRatioSourceTickHiAfterBit524288Int I := by
    simpa [getSqrtRatioSourceTickHiAfterBit524288Int] using
      sourceSqrtRatioStepInt_lb
        (getSqrtRatioSourceTickHiAbsTickInt I)
        (getSqrtRatioSourceTickHiAfterBit262144Int I)
        524288
        getSqrtRatioSourceFactor524288Int
        1404880482679654955896180642
        1404950724947776134837143967
        5800441176149320
        (by native_decide)
        (by native_decide)
        hr262144lo
        (by native_decide)
        (by native_decide)
  exact ne_of_gt (lt_of_lt_of_le (by norm_num) hr524288lo)

theorem getSqrtRatioAfterAllBitsWord_tickHi_ne_zero (I : ExecutionEnv) :
    getSqrtRatioAfterAllBitsWord
        (getSqrtRatioAbsTickBranchWord (getTickHiWord I))
        (getSqrtRatioInitialBranchWord
          (getSqrtRatioAbsTickBranchWord (getTickHiWord I))) ≠ ⟨0⟩ := by
  let absTick := getSqrtRatioAbsTickBranchWord (getTickHiWord I)
  let r0 := getSqrtRatioInitialBranchWord absTick
  let r0m := getSqrtRatioRatioMaskedWord r0
  have hr0mlo : 340265354078544963557816517032075149313 ≤ r0m.toNat := by
    dsimp [r0m, r0]
    exact getSqrtRatioInitialMaskedBranchWord_lb absTick
  have hr0mhi : r0m.toNat ≤ 2 ^ (128 : Nat) := by
    dsimp [r0m, r0]
    exact getSqrtRatioInitialMaskedBranchWord_le_q128 absTick
  let r2 := getSqrtRatioAfterBit2BranchWord absTick r0
  have hr2lo : 340231330945450418515964920540021147198 ≤ r2.toNat := by
    dsimp [r2]
    unfold getSqrtRatioAfterBit2BranchWord
    by_cases h : getSqrtRatioBit2Word absTick = ⟨0⟩
    · simpa [h, r0m, r0] using
        (le_trans (by native_decide :
          340231330945450418515964920540021147198 ≤
            340265354078544963557816517032075149313) hr0mlo)
    · simpa [h, getSqrtRatioAfterBit2Word, r0m, r0] using
        sqrtRatioStepWord_lb getSqrtRatioFactor2Word r0m
          340248342086729790484326174814286782778
          340265354078544963557816517032075149313
          340231330945450418515964920540021147198
          (by native_decide) (by native_decide) hr0mlo hr0mhi (by native_decide)
  have hr2hi : r2.toNat ≤ 2 ^ (128 : Nat) := by
    dsimp [r2]
    unfold getSqrtRatioAfterBit2BranchWord
    by_cases h : getSqrtRatioBit2Word absTick = ⟨0⟩
    · simpa [h, r0m, r0] using hr0mhi
    · simpa [h, getSqrtRatioAfterBit2Word, r0m, r0] using
        sqrtRatioStepWord_le_q128 getSqrtRatioFactor2Word r0m
          340248342086729790484326174814286782778
          (by native_decide) (by native_decide) hr0mhi
  let r4 := getSqrtRatioAfterBit4BranchWord absTick r2
  have hr4lo : 340163294884840501567246455576441303173 ≤ r4.toNat := by
    dsimp [r4]
    unfold getSqrtRatioAfterBit4BranchWord
    by_cases h : getSqrtRatioBit4Word absTick = ⟨0⟩
    · simpa [h] using
        (le_trans (by native_decide :
          340163294884840501567246455576441303173 ≤
            340231330945450418515964920540021147198) hr2lo)
    · simpa [h, getSqrtRatioAfterBit4Word] using
        sqrtRatioStepWord_lb getSqrtRatioFactor4Word r2
          340214320654664324051920982716015181260
          340231330945450418515964920540021147198
          340163294884840501567246455576441303173
          (by native_decide) (by native_decide) hr2lo hr2hi (by native_decide)
  have hr4hi : r4.toNat ≤ 2 ^ (128 : Nat) := by
    dsimp [r4]
    unfold getSqrtRatioAfterBit4BranchWord
    by_cases h : getSqrtRatioBit4Word absTick = ⟨0⟩
    · simpa [h] using hr2hi
    · simpa [h, getSqrtRatioAfterBit4Word] using
        sqrtRatioStepWord_le_q128 getSqrtRatioFactor4Word r2
          340214320654664324051920982716015181260
          (by native_decide) (by native_decide) hr2hi
  let r8 := getSqrtRatioAfterBit8BranchWord absTick r4
  have hr8lo : 340027263576413978334042125129128142263 ≤ r8.toNat := by
    dsimp [r8]
    unfold getSqrtRatioAfterBit8BranchWord
    by_cases h : getSqrtRatioBit8Word absTick = ⟨0⟩
    · simpa [h] using
        (le_trans (by native_decide :
          340027263576413978334042125129128142263 ≤
            340163294884840501567246455576441303173) hr4lo)
    · simpa [h, getSqrtRatioAfterBit8Word] using
        sqrtRatioStepWord_lb getSqrtRatioFactor8Word r4
          340146287995602323631171512101879684304
          340163294884840501567246455576441303173
          340027263576413978334042125129128142263
          (by native_decide) (by native_decide) hr4lo hr4hi (by native_decide)
  have hr8hi : r8.toNat ≤ 2 ^ (128 : Nat) := by
    dsimp [r8]
    unfold getSqrtRatioAfterBit8BranchWord
    by_cases h : getSqrtRatioBit8Word absTick = ⟨0⟩
    · simpa [h] using hr4hi
    · simpa [h, getSqrtRatioAfterBit8Word] using
        sqrtRatioStepWord_le_q128 getSqrtRatioFactor8Word r4
          340146287995602323631171512101879684304
          (by native_decide) (by native_decide) hr4hi
  let r16 := getSqrtRatioAfterBit16BranchWord absTick r8
  have hr16lo : 339755364134575681238502878529008278326 ≤ r16.toNat := by
    dsimp [r16]
    unfold getSqrtRatioAfterBit16BranchWord
    by_cases h : getSqrtRatioBit16Word absTick = ⟨0⟩
    · simpa [h] using
        (le_trans (by native_decide :
          339755364134575681238502878529008278326 ≤
            340027263576413978334042125129128142263) hr8lo)
    · simpa [h, getSqrtRatioAfterBit16Word] using
        sqrtRatioStepWord_lb getSqrtRatioFactor16Word r8
          340010263488231146823593991679159461444
          340027263576413978334042125129128142263
          339755364134575681238502878529008278326
          (by native_decide) (by native_decide) hr8lo hr8hi (by native_decide)
  have hr16hi : r16.toNat ≤ 2 ^ (128 : Nat) := by
    dsimp [r16]
    unfold getSqrtRatioAfterBit16BranchWord
    by_cases h : getSqrtRatioBit16Word absTick = ⟨0⟩
    · simpa [h] using hr8hi
    · simpa [h, getSqrtRatioAfterBit16Word] using
        sqrtRatioStepWord_le_q128 getSqrtRatioFactor16Word r8
          340010263488231146823593991679159461444
          (by native_decide) (by native_decide) hr8hi
  let r32 := getSqrtRatioAfterBit32BranchWord absTick r16
  have hr32lo : 339212217342146842559531600927033253847 ≤ r32.toNat := by
    dsimp [r32]
    unfold getSqrtRatioAfterBit32BranchWord
    by_cases h : getSqrtRatioBit32Word absTick = ⟨0⟩
    · simpa [h] using
        (le_trans (by native_decide :
          339212217342146842559531600927033253847 ≤
            339755364134575681238502878529008278326) hr16lo)
    · simpa [h, getSqrtRatioAfterBit32Word] using
        sqrtRatioStepWord_lb getSqrtRatioFactor32Word r16
          339738377640345403697157401104375502016
          339755364134575681238502878529008278326
          339212217342146842559531600927033253847
          (by native_decide) (by native_decide) hr16lo hr16hi (by native_decide)
  have hr32hi : r32.toNat ≤ 2 ^ (128 : Nat) := by
    dsimp [r32]
    unfold getSqrtRatioAfterBit32BranchWord
    by_cases h : getSqrtRatioBit32Word absTick = ⟨0⟩
    · simpa [h] using hr16hi
    · simpa [h, getSqrtRatioAfterBit32Word] using
        sqrtRatioStepWord_le_q128 getSqrtRatioFactor32Word r16
          339738377640345403697157401104375502016
          (by native_decide) (by native_decide) hr16hi
  let r64 := getSqrtRatioAfterBit64BranchWord absTick r32
  have hr64lo : 338128527259088467778511436198880488164 ≤ r64.toNat := by
    dsimp [r64]
    unfold getSqrtRatioAfterBit64BranchWord
    by_cases h : getSqrtRatioBit64Word absTick = ⟨0⟩
    · simpa [h] using
        (le_trans (by native_decide :
          338128527259088467778511436198880488164 ≤
            339212217342146842559531600927033253847) hr32lo)
    · simpa [h, getSqrtRatioAfterBit64Word] using
        sqrtRatioStepWord_lb getSqrtRatioFactor64Word r32
          339195258003219555707034227454543997025
          339212217342146842559531600927033253847
          338128527259088467778511436198880488164
          (by native_decide) (by native_decide) hr32lo hr32hi (by native_decide)
  have hr64hi : r64.toNat ≤ 2 ^ (128 : Nat) := by
    dsimp [r64]
    unfold getSqrtRatioAfterBit64BranchWord
    by_cases h : getSqrtRatioBit64Word absTick = ⟨0⟩
    · simpa [h] using hr32hi
    · simpa [h, getSqrtRatioAfterBit64Word] using
        sqrtRatioStepWord_le_q128 getSqrtRatioFactor64Word r32
          339195258003219555707034227454543997025
          (by native_decide) (by native_decide) hr32hi
  let r128 := getSqrtRatioAfterBit128BranchWord absTick r64
  have hr128lo : 335971522311117552149334092109581418674 ≤ r128.toNat := by
    dsimp [r128]
    unfold getSqrtRatioAfterBit128BranchWord
    by_cases h : getSqrtRatioBit128Word absTick = ⟨0⟩
    · simpa [h] using
        (le_trans (by native_decide :
          335971522311117552149334092109581418674 ≤
            338128527259088467778511436198880488164) hr64lo)
    · simpa [h, getSqrtRatioAfterBit128Word] using
        sqrtRatioStepWord_lb getSqrtRatioFactor128Word r64
          338111622100601834656805679988414885971
          338128527259088467778511436198880488164
          335971522311117552149334092109581418674
          (by native_decide) (by native_decide) hr64lo hr64hi (by native_decide)
  have hr128hi : r128.toNat ≤ 2 ^ (128 : Nat) := by
    dsimp [r128]
    unfold getSqrtRatioAfterBit128BranchWord
    by_cases h : getSqrtRatioBit128Word absTick = ⟨0⟩
    · simpa [h] using hr64hi
    · simpa [h, getSqrtRatioAfterBit128Word] using
        sqrtRatioStepWord_le_q128 getSqrtRatioFactor128Word r64
          338111622100601834656805679988414885971
          (by native_decide) (by native_decide) hr64hi
  let r256 := getSqrtRatioAfterBit256BranchWord absTick r128
  have hr256lo : 331698704829854243503582989311158516586 ≤ r256.toNat := by
    dsimp [r256]
    unfold getSqrtRatioAfterBit256BranchWord
    by_cases h : getSqrtRatioBit256Word absTick = ⟨0⟩
    · simpa [h] using
        (le_trans (by native_decide :
          331698704829854243503582989311158516586 ≤
            335971522311117552149334092109581418674) hr128lo)
    · simpa [h, getSqrtRatioAfterBit256Word] using
        sqrtRatioStepWord_lb getSqrtRatioFactor256Word r128
          335954724994790223023589805789778977700
          335971522311117552149334092109581418674
          331698704829854243503582989311158516586
          (by native_decide) (by native_decide) hr128lo hr128hi (by native_decide)
  have hr256hi : r256.toNat ≤ 2 ^ (128 : Nat) := by
    dsimp [r256]
    unfold getSqrtRatioAfterBit256BranchWord
    by_cases h : getSqrtRatioBit256Word absTick = ⟨0⟩
    · simpa [h] using hr128hi
    · simpa [h, getSqrtRatioAfterBit256Word] using
        sqrtRatioStepWord_le_q128 getSqrtRatioFactor256Word r128
          335954724994790223023589805789778977700
          (by native_decide) (by native_decide) hr128hi
  let r512 := getSqrtRatioAfterBit512BranchWord absTick r256
  have hr512lo : 323315401242583425022802937239550140918 ≤ r512.toNat := by
    dsimp [r512]
    unfold getSqrtRatioAfterBit512BranchWord
    by_cases h : getSqrtRatioBit512Word absTick = ⟨0⟩
    · simpa [h] using
        (le_trans (by native_decide :
          323315401242583425022802937239550140918 ≤
            331698704829854243503582989311158516586) hr256lo)
    · simpa [h, getSqrtRatioAfterBit512Word] using
        sqrtRatioStepWord_lb getSqrtRatioFactor512Word r256
          331682121138379247127172139078559817300
          331698704829854243503582989311158516586
          323315401242583425022802937239550140918
          (by native_decide) (by native_decide) hr256lo hr256hi (by native_decide)
  have hr512hi : r512.toNat ≤ 2 ^ (128 : Nat) := by
    dsimp [r512]
    unfold getSqrtRatioAfterBit512BranchWord
    by_cases h : getSqrtRatioBit512Word absTick = ⟨0⟩
    · simpa [h] using hr256hi
    · simpa [h, getSqrtRatioAfterBit512Word] using
        sqrtRatioStepWord_le_q128 getSqrtRatioFactor512Word r256
          331682121138379247127172139078559817300
          (by native_decide) (by native_decide) hr256hi
  let r1024 := getSqrtRatioAfterBit1024BranchWord absTick r512
  have hr1024lo : 307179074178916392659402722612948179612 ≤ r1024.toNat := by
    dsimp [r1024]
    unfold getSqrtRatioAfterBit1024BranchWord
    by_cases h : getSqrtRatioBit1024Word absTick = ⟨0⟩
    · simpa [h] using
        (le_trans (by native_decide :
          307179074178916392659402722612948179612 ≤
            323315401242583425022802937239550140918) hr512lo)
    · simpa [h, getSqrtRatioAfterBit1024Word] using
        sqrtRatioStepWord_lb getSqrtRatioFactor1024Word r512
          323299236684853023288211250268160618739
          323315401242583425022802937239550140918
          307179074178916392659402722612948179612
          (by native_decide) (by native_decide) hr512lo hr512hi (by native_decide)
  have hr1024hi : r1024.toNat ≤ 2 ^ (128 : Nat) := by
    dsimp [r1024]
    unfold getSqrtRatioAfterBit1024BranchWord
    by_cases h : getSqrtRatioBit1024Word absTick = ⟨0⟩
    · simpa [h] using hr512hi
    · simpa [h, getSqrtRatioAfterBit1024Word] using
        sqrtRatioStepWord_le_q128 getSqrtRatioFactor1024Word r512
          323299236684853023288211250268160618739
          (by native_decide) (by native_decide) hr512hi
  let r2048 := getSqrtRatioAfterBit2048BranchWord absTick r1024
  have hr2048lo : 277282266700509388632609933215391170106 ≤ r2048.toNat := by
    dsimp [r2048]
    unfold getSqrtRatioAfterBit2048BranchWord
    by_cases h : getSqrtRatioBit2048Word absTick = ⟨0⟩
    · simpa [h] using
        (le_trans (by native_decide :
          277282266700509388632609933215391170106 ≤
            307179074178916392659402722612948179612) hr1024lo)
    · simpa [h, getSqrtRatioAfterBit2048Word] using
        sqrtRatioStepWord_lb getSqrtRatioFactor2048Word r1024
          307163716377032989948697243942600083929
          307179074178916392659402722612948179612
          277282266700509388632609933215391170106
          (by native_decide) (by native_decide) hr1024lo hr1024hi (by native_decide)
  have hr2048hi : r2048.toNat ≤ 2 ^ (128 : Nat) := by
    dsimp [r2048]
    unfold getSqrtRatioAfterBit2048BranchWord
    by_cases h : getSqrtRatioBit2048Word absTick = ⟨0⟩
    · simpa [h] using hr1024hi
    · simpa [h, getSqrtRatioAfterBit2048Word] using
        sqrtRatioStepWord_le_q128 getSqrtRatioFactor2048Word r1024
          307163716377032989948697243942600083929
          (by native_decide) (by native_decide) hr1024hi
  let r4096 := getSqrtRatioAfterBit4096BranchWord absTick r2048
  have hr4096lo : 225934749830749445986089663015556949343 ≤ r4096.toNat := by
    dsimp [r4096]
    unfold getSqrtRatioAfterBit4096BranchWord
    by_cases h : getSqrtRatioBit4096Word absTick = ⟨0⟩
    · simpa [h] using
        (le_trans (by native_decide :
          225934749830749445986089663015556949343 ≤
            277282266700509388632609933215391170106) hr2048lo)
    · simpa [h, getSqrtRatioAfterBit4096Word] using
        sqrtRatioStepWord_lb getSqrtRatioFactor4096Word r2048
          277268403626896220162999269216087595045
          277282266700509388632609933215391170106
          225934749830749445986089663015556949343
          (by native_decide) (by native_decide) hr2048lo hr2048hi (by native_decide)
  have hr4096hi : r4096.toNat ≤ 2 ^ (128 : Nat) := by
    dsimp [r4096]
    unfold getSqrtRatioAfterBit4096BranchWord
    by_cases h : getSqrtRatioBit4096Word absTick = ⟨0⟩
    · simpa [h] using hr2048hi
    · simpa [h, getSqrtRatioAfterBit4096Word] using
        sqrtRatioStepWord_le_q128 getSqrtRatioFactor4096Word r2048
          277268403626896220162999269216087595045
          (by native_decide) (by native_decide) hr2048hi
  let r8192 := getSqrtRatioAfterBit8192BranchWord absTick r4096
  have hr8192lo : 150004713758184102711002566140788444796 ≤ r8192.toNat := by
    dsimp [r8192]
    unfold getSqrtRatioAfterBit8192BranchWord
    by_cases h : getSqrtRatioBit8192Word absTick = ⟨0⟩
    · simpa [h] using
        (le_trans (by native_decide :
          150004713758184102711002566140788444796 ≤
            225934749830749445986089663015556949343) hr4096lo)
    · simpa [h, getSqrtRatioAfterBit8192Word] using
        sqrtRatioStepWord_lb getSqrtRatioFactor8192Word r4096
          225923453940442621947126027127485391333
          225934749830749445986089663015556949343
          150004713758184102711002566140788444796
          (by native_decide) (by native_decide) hr4096lo hr4096hi (by native_decide)
  have hr8192hi : r8192.toNat ≤ 2 ^ (128 : Nat) := by
    dsimp [r8192]
    unfold getSqrtRatioAfterBit8192BranchWord
    by_cases h : getSqrtRatioBit8192Word absTick = ⟨0⟩
    · simpa [h] using hr4096hi
    · simpa [h, getSqrtRatioAfterBit8192Word] using
        sqrtRatioStepWord_le_q128 getSqrtRatioFactor8192Word r4096
          225923453940442621947126027127485391333
          (by native_decide) (by native_decide) hr4096hi
  let r16384 := getSqrtRatioAfterBit16384BranchWord absTick r8192
  have hr16384lo : 66122407008436832627027740713496573148 ≤ r16384.toNat := by
    dsimp [r16384]
    unfold getSqrtRatioAfterBit16384BranchWord
    by_cases h : getSqrtRatioBit16384Word absTick = ⟨0⟩
    · simpa [h] using
        (le_trans (by native_decide :
          66122407008436832627027740713496573148 ≤
            150004713758184102711002566140788444796) hr8192lo)
    · simpa [h, getSqrtRatioAfterBit16384Word] using
        sqrtRatioStepWord_lb getSqrtRatioFactor16384Word r8192
          149997214084966997727330242082538205943
          150004713758184102711002566140788444796
          66122407008436832627027740713496573148
          (by native_decide) (by native_decide) hr8192lo hr8192hi (by native_decide)
  have hr16384hi : r16384.toNat ≤ 2 ^ (128 : Nat) := by
    dsimp [r16384]
    unfold getSqrtRatioAfterBit16384BranchWord
    by_cases h : getSqrtRatioBit16384Word absTick = ⟨0⟩
    · simpa [h] using hr8192hi
    · simpa [h, getSqrtRatioAfterBit16384Word] using
        sqrtRatioStepWord_le_q128 getSqrtRatioFactor16384Word r8192
          149997214084966997727330242082538205943
          (by native_decide) (by native_decide) hr8192hi
  let r32768 := getSqrtRatioAfterBit32768BranchWord absTick r16384
  have hr32768lo : 12848018414553970828728179856918040433 ≤ r32768.toNat := by
    dsimp [r32768]
    unfold getSqrtRatioAfterBit32768BranchWord
    by_cases h : getSqrtRatioBit32768Word absTick = ⟨0⟩
    · simpa [h] using
        (le_trans (by native_decide :
          12848018414553970828728179856918040433 ≤
            66122407008436832627027740713496573148) hr16384lo)
    · simpa [h, getSqrtRatioAfterBit32768Word] using
        sqrtRatioStepWord_lb getSqrtRatioFactor32768Word r16384
          66119101136024775622716233608466517926
          66122407008436832627027740713496573148
          12848018414553970828728179856918040433
          (by native_decide) (by native_decide) hr16384lo hr16384hi (by native_decide)
  have hr32768hi : r32768.toNat ≤ 2 ^ (128 : Nat) := by
    dsimp [r32768]
    unfold getSqrtRatioAfterBit32768BranchWord
    by_cases h : getSqrtRatioBit32768Word absTick = ⟨0⟩
    · simpa [h] using hr16384hi
    · simpa [h, getSqrtRatioAfterBit32768Word] using
        sqrtRatioStepWord_le_q128 getSqrtRatioFactor32768Word r16384
          66119101136024775622716233608466517926
          (by native_decide) (by native_decide) hr16384hi
  let r65536 := getSqrtRatioAfterBit65536BranchWord absTick r32768
  have hr65536lo : 485077512873820763967752669154895175 ≤ r65536.toNat := by
    dsimp [r65536]
    unfold getSqrtRatioAfterBit65536BranchWord
    by_cases h : getSqrtRatioBit65536Word absTick = ⟨0⟩
    · simpa [h] using
        (le_trans (by native_decide :
          485077512873820763967752669154895175 ≤
            12848018414553970828728179856918040433) hr32768lo)
    · simpa [h, getSqrtRatioAfterBit65536Word] using
        sqrtRatioStepWord_lb getSqrtRatioFactor65536Word r32768
          12847376061809297530290974190478138313
          12848018414553970828728179856918040433
          485077512873820763967752669154895175
          (by native_decide) (by native_decide) hr32768lo hr32768hi (by native_decide)
  have hr65536hi : r65536.toNat ≤ 2 ^ (128 : Nat) := by
    dsimp [r65536]
    unfold getSqrtRatioAfterBit65536BranchWord
    by_cases h : getSqrtRatioBit65536Word absTick = ⟨0⟩
    · simpa [h] using hr32768hi
    · simpa [h, getSqrtRatioAfterBit65536Word] using
        sqrtRatioStepWord_le_q128 getSqrtRatioFactor65536Word r32768
          12847376061809297530290974190478138313
          (by native_decide) (by native_decide) hr32768hi
  let r131072 := getSqrtRatioAfterBit131072BranchWord absTick r65536
  have hr131072lo : 691450548841240133896843047535567 ≤ r131072.toNat := by
    dsimp [r131072]
    unfold getSqrtRatioAfterBit131072BranchWord
    by_cases h : getSqrtRatioBit131072Word absTick = ⟨0⟩
    · simpa [h] using
        (le_trans (by native_decide :
          691450548841240133896843047535567 ≤
            485077512873820763967752669154895175) hr65536lo)
    · simpa [h, getSqrtRatioAfterBit131072Word] using
        sqrtRatioStepWord_lb getSqrtRatioFactor131072Word r65536
          485053260817066172746253684029974020
          485077512873820763967752669154895175
          691450548841240133896843047535567
          (by native_decide) (by native_decide) hr65536lo hr65536hi (by native_decide)
  have hr131072hi : r131072.toNat ≤ 2 ^ (128 : Nat) := by
    dsimp [r131072]
    unfold getSqrtRatioAfterBit131072BranchWord
    by_cases h : getSqrtRatioBit131072Word absTick = ⟨0⟩
    · simpa [h] using hr65536hi
    · simpa [h, getSqrtRatioAfterBit131072Word] using
        sqrtRatioStepWord_le_q128 getSqrtRatioFactor131072Word r65536
          485053260817066172746253684029974020
          (by native_decide) (by native_decide) hr65536hi
  let r262144 := getSqrtRatioAfterBit262144BranchWord absTick r131072
  have hr262144lo : 1404950724947776134837143967 ≤ r262144.toNat := by
    dsimp [r262144]
    unfold getSqrtRatioAfterBit262144BranchWord
    by_cases h : getSqrtRatioBit262144Word absTick = ⟨0⟩
    · simpa [h] using
        (le_trans (by native_decide :
          1404950724947776134837143967 ≤
            691450548841240133896843047535567) hr131072lo)
    · simpa [h, getSqrtRatioAfterBit262144Word] using
        sqrtRatioStepWord_lb getSqrtRatioFactor262144Word r131072
          691415978906521570653435304214168
          691450548841240133896843047535567
          1404950724947776134837143967
          (by native_decide) (by native_decide) hr131072lo hr131072hi (by native_decide)
  have hr262144hi : r262144.toNat ≤ 2 ^ (128 : Nat) := by
    dsimp [r262144]
    unfold getSqrtRatioAfterBit262144BranchWord
    by_cases h : getSqrtRatioBit262144Word absTick = ⟨0⟩
    · simpa [h] using hr131072hi
    · simpa [h, getSqrtRatioAfterBit262144Word] using
        sqrtRatioStepWord_le_q128 getSqrtRatioFactor262144Word r131072
          691415978906521570653435304214168
          (by native_decide) (by native_decide) hr131072hi
  let r524288 := getSqrtRatioAfterBit524288BranchWord absTick r262144
  have hr524288lo : 5800441176149320 ≤ r524288.toNat := by
    dsimp [r524288]
    unfold getSqrtRatioAfterBit524288BranchWord
    by_cases h : getSqrtRatioBit524288Word absTick = ⟨0⟩
    · simpa [h] using
        (le_trans (by native_decide :
          5800441176149320 ≤ 1404950724947776134837143967) hr262144lo)
    · simpa [h, getSqrtRatioAfterBit524288Word] using
        sqrtRatioStepWord_lb getSqrtRatioFactor524288Word r262144
          1404880482679654955896180642
          1404950724947776134837143967
          5800441176149320
          (by native_decide) (by native_decide) hr262144lo hr262144hi (by native_decide)
  change r524288 ≠ ⟨0⟩
  intro hzero
  have hz : r524288.toNat = 0 := by
    simpa using congrArg UInt256.toNat hzero
  have hpos : 0 < r524288.toNat :=
    lt_of_lt_of_le (by native_decide : 0 < 5800441176149320) hr524288lo
  omega

end Benchmarks.UniswapV3Pool

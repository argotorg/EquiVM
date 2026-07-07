import Benchmarks.UniswapV3Pool.InitializeSourceGetTickMsb

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

theorem initializeArgWord_toNat_lt_twoPow160 (I : ExecutionEnv) :
    (initializeArgWord I).toNat < 2 ^ (160 : Nat) := by
  unfold initializeArgWord
  rw [initializeUint160Mask_decode]
  exact Nat.mod_lt _ (by norm_num [EVM.twoPow])

theorem getTickSourceRatioNat_lt_twoPow192 (I : ExecutionEnv) :
    getTickSourceRatioNat I < 2 ^ (192 : Nat) := by
  unfold getTickSourceRatioNat
  rw [Nat.mod_eq_of_lt]
  · have harg := initializeArgWord_toNat_lt_twoPow160 I
    have hmul := Nat.mul_lt_mul_of_pos_right harg (by norm_num : 0 < 2 ^ (32 : Nat))
    rw [← Nat.pow_add] at hmul
    norm_num at hmul
    exact hmul
  · have harg := initializeArgWord_toNat_lt_twoPow160 I
    have hmul := Nat.mul_lt_mul_of_pos_right harg (by norm_num : 0 < 2 ^ (32 : Nat))
    rw [← Nat.pow_add] at hmul
    norm_num at hmul ⊢
    exact lt_trans hmul (by norm_num [EVM.wordModulus, EVM.twoPow])

theorem getTickSourceRAfterMsb7Nat_le_threshold7 (I : ExecutionEnv) :
    getTickSourceRAfterMsb7Nat I ≤ 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF := by
  unfold getTickSourceRAfterMsb7Nat getTickSourceMsbF7Nat getTickSourceRatioGt7
  by_cases h : getTickSourceRatioNat I > 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  · rw [show decide (getTickSourceRatioNat I > 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) =
      true by exact decide_eq_true h]
    norm_num
    rw [Nat.div_le_iff_le_mul (by norm_num)]
    have hratio := getTickSourceRatioNat_lt_twoPow192 I
    norm_num at hratio ⊢
    omega
  · rw [show decide (getTickSourceRatioNat I > 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) =
      false by exact decide_eq_false h]
    norm_num
    omega

theorem getTickSourceRAfterMsb6Nat_le_threshold6 (I : ExecutionEnv) :
    getTickSourceRAfterMsb6Nat I ≤ 0xFFFFFFFFFFFFFFFF := by
  unfold getTickSourceRAfterMsb6Nat getTickSourceMsbF6Nat getTickSourceRAfterMsb7Gt6
  by_cases h : getTickSourceRAfterMsb7Nat I > 0xFFFFFFFFFFFFFFFF
  · rw [show decide (getTickSourceRAfterMsb7Nat I > 0xFFFFFFFFFFFFFFFF) =
      true by exact decide_eq_true h]
    norm_num
    rw [Nat.div_le_iff_le_mul (by norm_num)]
    have hprev := getTickSourceRAfterMsb7Nat_le_threshold7 I
    norm_num at hprev ⊢
    omega
  · rw [show decide (getTickSourceRAfterMsb7Nat I > 0xFFFFFFFFFFFFFFFF) =
      false by exact decide_eq_false h]
    norm_num
    omega

theorem getTickSourceRAfterMsb5Nat_le_threshold5 (I : ExecutionEnv) :
    getTickSourceRAfterMsb5Nat I ≤ 0xFFFFFFFF := by
  unfold getTickSourceRAfterMsb5Nat getTickSourceMsbF5Nat getTickSourceRAfterMsb6Gt5
  by_cases h : getTickSourceRAfterMsb6Nat I > 0xFFFFFFFF
  · rw [show decide (getTickSourceRAfterMsb6Nat I > 0xFFFFFFFF) =
      true by exact decide_eq_true h]
    norm_num
    rw [Nat.div_le_iff_le_mul (by norm_num)]
    have hprev := getTickSourceRAfterMsb6Nat_le_threshold6 I
    norm_num at hprev ⊢
    omega
  · rw [show decide (getTickSourceRAfterMsb6Nat I > 0xFFFFFFFF) =
      false by exact decide_eq_false h]
    norm_num
    omega

theorem getTickSourceRAfterMsb4Nat_le_threshold3 (I : ExecutionEnv) :
    getTickSourceRAfterMsb4Nat I ≤ 0xFFFF := by
  unfold getTickSourceRAfterMsb4Nat getTickSourceMsbF4Nat getTickSourceRAfterMsb5Gt4
  by_cases h : getTickSourceRAfterMsb5Nat I > 0xFFFF
  · rw [show decide (getTickSourceRAfterMsb5Nat I > 0xFFFF) =
      true by exact decide_eq_true h]
    norm_num
    rw [Nat.div_le_iff_le_mul (by norm_num)]
    have hprev := getTickSourceRAfterMsb5Nat_le_threshold5 I
    norm_num at hprev ⊢
    omega
  · rw [show decide (getTickSourceRAfterMsb5Nat I > 0xFFFF) =
      false by exact decide_eq_false h]
    norm_num
    omega

theorem getTickSourceRAfterMsb3Nat_le_threshold2 (I : ExecutionEnv) :
    getTickSourceRAfterMsb3Nat I ≤ 0xFF := by
  unfold getTickSourceRAfterMsb3Nat getTickSourceMsbF3Nat getTickSourceRAfterMsb4Gt3
  by_cases h : getTickSourceRAfterMsb4Nat I > 0xFF
  · rw [show decide (getTickSourceRAfterMsb4Nat I > 0xFF) =
      true by exact decide_eq_true h]
    norm_num
    rw [Nat.div_le_iff_le_mul (by norm_num)]
    have hprev := getTickSourceRAfterMsb4Nat_le_threshold3 I
    norm_num at hprev ⊢
    omega
  · rw [show decide (getTickSourceRAfterMsb4Nat I > 0xFF) =
      false by exact decide_eq_false h]
    norm_num
    omega

theorem getTickSourceRAfterMsb2Nat_le_threshold1 (I : ExecutionEnv) :
    getTickSourceRAfterMsb2Nat I ≤ 0xF := by
  unfold getTickSourceRAfterMsb2Nat getTickSourceMsbF2Nat getTickSourceRAfterMsb3Gt2
  by_cases h : getTickSourceRAfterMsb3Nat I > 0xF
  · rw [show decide (getTickSourceRAfterMsb3Nat I > 0xF) =
      true by exact decide_eq_true h]
    norm_num
    rw [Nat.div_le_iff_le_mul (by norm_num)]
    have hprev := getTickSourceRAfterMsb3Nat_le_threshold2 I
    norm_num at hprev ⊢
    omega
  · rw [show decide (getTickSourceRAfterMsb3Nat I > 0xF) =
      false by exact decide_eq_false h]
    norm_num
    omega

theorem getTickSourceRAfterMsb1Nat_le_3 (I : ExecutionEnv) :
    getTickSourceRAfterMsb1Nat I ≤ 3 := by
  unfold getTickSourceRAfterMsb1Nat getTickSourceMsbF1Nat getTickSourceRAfterMsb2Gt1
  by_cases h : getTickSourceRAfterMsb2Nat I > 0x3
  · rw [show decide (getTickSourceRAfterMsb2Nat I > 0x3) =
      true by exact decide_eq_true h]
    norm_num
    rw [Nat.div_le_iff_le_mul (by norm_num)]
    have hprev := getTickSourceRAfterMsb2Nat_le_threshold1 I
    norm_num at hprev ⊢
    omega
  · rw [show decide (getTickSourceRAfterMsb2Nat I > 0x3) =
      false by exact decide_eq_false h]
    norm_num
    omega

theorem getTickSourceRAfterMsb6Nat_eq_ratio_div_msbAfter6 (I : ExecutionEnv) :
    getTickSourceRAfterMsb6Nat I =
      getTickSourceRatioNat I / 2 ^ getTickSourceMsbAfter6Nat I := by
  unfold getTickSourceRAfterMsb6Nat getTickSourceRAfterMsb7Nat getTickSourceMsbAfter6Nat
  rw [Nat.div_div_eq_div_mul]
  rw [← Nat.pow_add]

theorem getTickSourceRAfterMsb5Nat_eq_ratio_div_msbAfter5 (I : ExecutionEnv) :
    getTickSourceRAfterMsb5Nat I =
      getTickSourceRatioNat I / 2 ^ getTickSourceMsbAfter5Nat I := by
  unfold getTickSourceRAfterMsb5Nat getTickSourceMsbAfter5Nat
  rw [getTickSourceRAfterMsb6Nat_eq_ratio_div_msbAfter6]
  rw [Nat.div_div_eq_div_mul]
  rw [← Nat.pow_add]

theorem getTickSourceRAfterMsb4Nat_eq_ratio_div_msbAfter4 (I : ExecutionEnv) :
    getTickSourceRAfterMsb4Nat I =
      getTickSourceRatioNat I / 2 ^ getTickSourceMsbAfter4Nat I := by
  unfold getTickSourceRAfterMsb4Nat getTickSourceMsbAfter4Nat
  rw [getTickSourceRAfterMsb5Nat_eq_ratio_div_msbAfter5]
  rw [Nat.div_div_eq_div_mul]
  rw [← Nat.pow_add]

theorem getTickSourceRAfterMsb3Nat_eq_ratio_div_msbAfter3 (I : ExecutionEnv) :
    getTickSourceRAfterMsb3Nat I =
      getTickSourceRatioNat I / 2 ^ getTickSourceMsbAfter3Nat I := by
  unfold getTickSourceRAfterMsb3Nat getTickSourceMsbAfter3Nat
  rw [getTickSourceRAfterMsb4Nat_eq_ratio_div_msbAfter4]
  rw [Nat.div_div_eq_div_mul]
  rw [← Nat.pow_add]

theorem getTickSourceRAfterMsb2Nat_eq_ratio_div_msbAfter2 (I : ExecutionEnv) :
    getTickSourceRAfterMsb2Nat I =
      getTickSourceRatioNat I / 2 ^ getTickSourceMsbAfter2Nat I := by
  unfold getTickSourceRAfterMsb2Nat getTickSourceMsbAfter2Nat
  rw [getTickSourceRAfterMsb3Nat_eq_ratio_div_msbAfter3]
  rw [Nat.div_div_eq_div_mul]
  rw [← Nat.pow_add]

theorem getTickSourceRAfterMsb1Nat_eq_ratio_div_msbAfter1 (I : ExecutionEnv) :
    getTickSourceRAfterMsb1Nat I =
      getTickSourceRatioNat I / 2 ^ getTickSourceMsbAfter1Nat I := by
  unfold getTickSourceRAfterMsb1Nat getTickSourceMsbAfter1Nat
  rw [getTickSourceRAfterMsb2Nat_eq_ratio_div_msbAfter2]
  rw [Nat.div_div_eq_div_mul]
  rw [← Nat.pow_add]

theorem getTickSourceRAfterMsb1Nat_lt_twoPow_f0_succ (I : ExecutionEnv) :
    getTickSourceRAfterMsb1Nat I < 2 ^ (getTickSourceMsbF0Nat I + 1) := by
  unfold getTickSourceMsbF0Nat getTickSourceRAfterMsb1Gt0
  by_cases h : getTickSourceRAfterMsb1Nat I > 1
  · rw [show decide (getTickSourceRAfterMsb1Nat I > 1) = true by exact decide_eq_true h]
    have hle := getTickSourceRAfterMsb1Nat_le_3 I
    norm_num
    omega
  · rw [show decide (getTickSourceRAfterMsb1Nat I > 1) = false by exact decide_eq_false h]
    norm_num
    omega

theorem getTickSourceRatioNat_lt_twoPow_msbAfter0_succ (I : ExecutionEnv) :
    getTickSourceRatioNat I < 2 ^ (getTickSourceMsbAfter0Nat I + 1) := by
  have hdiv := getTickSourceRAfterMsb1Nat_lt_twoPow_f0_succ I
  rw [getTickSourceRAfterMsb1Nat_eq_ratio_div_msbAfter1] at hdiv
  have hk : 0 < 2 ^ getTickSourceMsbAfter1Nat I := Nat.pow_pos (by norm_num)
  have hratio := (Nat.div_lt_iff_lt_mul hk).mp hdiv
  rw [← Nat.pow_add] at hratio
  have hexp :
      getTickSourceMsbF0Nat I + 1 + getTickSourceMsbAfter1Nat I =
        getTickSourceMsbAfter1Nat I + getTickSourceMsbF0Nat I + 1 := by
    omega
  rw [hexp] at hratio
  simpa [getTickSourceMsbAfter0Nat] using hratio

theorem getTickSourceRNormalizedHighNat_lt_twoPow128 (I : ExecutionEnv)
    (hge : getTickSourceMsbGe128 I = true) :
    getTickSourceRNormalizedHighNat I < 2 ^ (128 : Nat) := by
  have hNat : 128 ≤ getTickSourceMsbAfter0Nat I := by
    unfold getTickSourceMsbGe128 at hge
    exact of_decide_eq_true hge
  unfold getTickSourceRNormalizedHighNat
  rw [Nat.div_lt_iff_lt_mul (by
    exact Nat.pow_pos (by norm_num : 0 < 2))]
  rw [← Nat.pow_add]
  have hexp : 128 + (getTickSourceMsbAfter0Nat I - 127) =
      getTickSourceMsbAfter0Nat I + 1 := by
    omega
  rw [hexp]
  exact getTickSourceRatioNat_lt_twoPow_msbAfter0_succ I

theorem getTickSourceRNormalizedLowNat_lt_twoPow128 (I : ExecutionEnv)
    (hge : getTickSourceMsbGe128 I = false) :
    getTickSourceRNormalizedLowNat I < 2 ^ (128 : Nat) := by
  have hNat : getTickSourceMsbAfter0Nat I < 128 := by
    unfold getTickSourceMsbGe128 at hge
    exact Nat.lt_of_not_ge (of_decide_eq_false hge)
  unfold getTickSourceRNormalizedLowNat
  have hratio := getTickSourceRatioNat_lt_twoPow_msbAfter0_succ I
  have hmul := Nat.mul_lt_mul_of_pos_right hratio
    (k := 2 ^ (127 - getTickSourceMsbAfter0Nat I))
    (Nat.pow_pos (by norm_num : 0 < 2))
  rw [← Nat.pow_add] at hmul
  have hexp : getTickSourceMsbAfter0Nat I + 1 + (127 - getTickSourceMsbAfter0Nat I) =
      128 := by
    omega
  rw [hexp] at hmul
  rw [Nat.mod_eq_of_lt]
  · exact hmul
  · exact lt_trans hmul (by norm_num [EVM.wordModulus, EVM.twoPow])

theorem getTickSourceRNormalizedNat_lt_twoPow128 (I : ExecutionEnv) :
    getTickSourceRNormalizedNat I < 2 ^ (128 : Nat) := by
  unfold getTickSourceRNormalizedNat
  by_cases hge : getTickSourceMsbGe128 I = true
  · rw [if_pos hge]
    exact getTickSourceRNormalizedHighNat_lt_twoPow128 I hge
  · have hfalse : getTickSourceMsbGe128 I = false := Bool.eq_false_iff.mpr hge
    rw [if_neg hge]
    exact getTickSourceRNormalizedLowNat_lt_twoPow128 I hfalse

theorem getTickSourceRNormalizedNat_mul_self_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceRNormalizedNat I * getTickSourceRNormalizedNat I < EVM.wordModulus := by
  have hr := getTickSourceRNormalizedNat_lt_twoPow128 I
  have hrle : getTickSourceRNormalizedNat I ≤ 2 ^ (128 : Nat) - 1 :=
    Nat.le_pred_of_lt hr
  have hmul := Nat.mul_le_mul hrle hrle
  exact Nat.lt_of_le_of_lt hmul (by norm_num [EVM.wordModulus, EVM.twoPow])

theorem intOfNat_toNat_div_pow_127_cast (n : Nat) :
    ((Int.ofNat n).toNat / 2 ^ Int.toNat (127 : Int) : Int) =
      (n / 2 ^ (127 : Nat) : Nat) := by
  rfl

def getTickSourceLogRShifted63Nat (I : ExecutionEnv) : Nat :=
  getTickSourceRNormalizedNat I * getTickSourceRNormalizedNat I / 2 ^ (127 : Nat)

def getTickSourceLogRShifted63Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceLogRShifted63Nat I)

def getTickStoreAfterLogRShifted63 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterLog2BaseLet I).insert "r" (getTickSourceLogRShifted63Value I)

def getTickSourceLogF63Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogRShifted63Nat I / 2 ^ (128 : Nat)

def getTickSourceLogF63Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceLogF63Nat I)

def getTickStoreAfterLogF63Let (I : ExecutionEnv) : Store :=
  (getTickStoreAfterLogRShifted63 I).insert "f" (getTickSourceLogF63Value I)

def getTickSourceLog2After63Int (I : ExecutionEnv) : Int :=
  getTickSourceLog2BaseInt I + (getTickSourceLogF63Nat I : Int) * (2 ^ (63 : Nat) : Int)

def getTickSourceLog2After63Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceLog2After63Int I)

def getTickStoreAfterLog2Step63 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterLogF63Let I).insert "log_2" (getTickSourceLog2After63Value I)

def getTickSourceLogRAfter63Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogRShifted63Nat I / 2 ^ getTickSourceLogF63Nat I

def getTickSourceLogRAfter63Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceLogRAfter63Nat I)

def getTickStoreAfterLogStep63 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterLog2Step63 I).insert "r" (getTickSourceLogRAfter63Value I)

theorem getTickSourceLogRShifted63Nat_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceLogRShifted63Nat I < EVM.wordModulus := by
  unfold getTickSourceLogRShifted63Nat
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (getTickSourceRNormalizedNat_mul_self_lt_wordModulus I)

theorem getTickSourceLogRShifted63Nat_lt_twoPow129 (I : ExecutionEnv) :
    getTickSourceLogRShifted63Nat I < 2 ^ (129 : Nat) := by
  unfold getTickSourceLogRShifted63Nat
  rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ (127 : Nat))]
  rw [← Nat.pow_add]
  norm_num
  exact getTickSourceRNormalizedNat_mul_self_lt_wordModulus I

theorem getTickSourceLogF63Nat_le_1 (I : ExecutionEnv) :
    getTickSourceLogF63Nat I ≤ 1 := by
  unfold getTickSourceLogF63Nat
  have hshifted := getTickSourceLogRShifted63Nat_lt_twoPow129 I
  have hf : getTickSourceLogRShifted63Nat I / 2 ^ (128 : Nat) < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ (128 : Nat))]
    norm_num
    exact hshifted
  omega

theorem getTickStoreAfterNormalizeR_r (I : ExecutionEnv) :
    (getTickStoreAfterNormalizeR I).get? "r" =
      some (getTickSourceRNormalizedValue I) := by
  rw [getTickStoreAfterNormalizeR, store_get_self]

theorem getTickStoreAfterLog2BaseLet_r (I : ExecutionEnv) :
    (getTickStoreAfterLog2BaseLet I).get? "r" =
      some (getTickSourceRNormalizedValue I) := by
  rw [getTickStoreAfterLog2BaseLet]
  rw [store_get_ne (getTickStoreAfterNormalizeR I) (k := "log_2") (a := "r")
    (getTickSourceLog2BaseValue I) (by decide)]
  exact getTickStoreAfterNormalizeR_r I

theorem getTickStoreAfterLog2BaseLet_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLog2BaseLet I).get? "log_2" =
      some (getTickSourceLog2BaseValue I) := by
  rw [getTickStoreAfterLog2BaseLet, store_get_self]

theorem evalExpr_getTick_rVar_afterLog2Base {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLog2BaseLet I }
      evm (.var "r") = .ok (getTickSourceRNormalizedValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterLog2BaseLet_r]

theorem evalExpr_getTick_log2Var_afterLog2Base {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLog2BaseLet I }
      evm (.var "log_2") = .ok (getTickSourceLog2BaseValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterLog2BaseLet_log2]

theorem evalExpr_getTick_log_r_mul_r_63 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLog2BaseLet I }
      evm (mulE (.var "r") (.var "r")) =
      .ok (.int (Int.ofNat (getTickSourceRNormalizedNat I * getTickSourceRNormalizedNat I))) := by
  unfold mulE
  simp only [evalExpr?, evalExpr_getTick_rVar_afterLog2Base, EvalResult.bind, bind,
    evalBinaryOp?, getTickSourceRNormalizedValue]
  rw [← Int.natCast_mul]
  rfl

theorem evalExpr_getTick_log_r_shifted_63 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLog2BaseLet I }
      evm (shrE (mulE (.var "r") (.var "r")) (.intLit 127)) =
      .ok (getTickSourceLogRShifted63Value I) := by
  unfold shrE
  simp only [evalExpr?, evalExpr_getTick_log_r_mul_r_63, EvalResult.bind, bind, pure]
  rw [evalBinaryOp_int_shr_ok]
  · rw [getTickSourceLogRShifted63Value, getTickSourceLogRShifted63Nat]
    rw [intOfNat_toNat_div_pow_127_cast]
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_lt.mpr (getTickSourceRNormalizedNat_mul_self_lt_wordModulus I)
  · norm_num
  · norm_num

theorem assignStorageRef_getTick_r_shifted63 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterLog2BaseLet I }
      evm .localVar (varRef "r") (getTickSourceLogRShifted63Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterLogRShifted63 I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterLog2BaseLet_r]
  simp [getTickStoreAfterLogRShifted63, updateLocalPath?, pure, bind, EvalResult.bind]

theorem getTickStoreAfterLogRShifted63_r (I : ExecutionEnv) :
    (getTickStoreAfterLogRShifted63 I).get? "r" =
      some (getTickSourceLogRShifted63Value I) := by
  rw [getTickStoreAfterLogRShifted63, store_get_self]

theorem getTickStoreAfterLogRShifted63_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogRShifted63 I).get? "log_2" =
      some (getTickSourceLog2BaseValue I) := by
  rw [getTickStoreAfterLogRShifted63]
  rw [store_get_ne (getTickStoreAfterLog2BaseLet I) (k := "r") (a := "log_2")
    (getTickSourceLogRShifted63Value I) (by decide)]
  exact getTickStoreAfterLog2BaseLet_log2 I

theorem evalExpr_getTick_rVar_afterLogRShifted63 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogRShifted63 I }
      evm (.var "r") = .ok (getTickSourceLogRShifted63Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterLogRShifted63_r]

theorem evalExpr_getTick_log_f63 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogRShifted63 I }
      evm (shrE (.var "r") shift128) = .ok (getTickSourceLogF63Value I) := by
  unfold shrE shift128
  simp only [evalExpr?, evalExpr_getTick_rVar_afterLogRShifted63, EvalResult.bind, bind, pure]
  change evalBinaryOp? .shr (.int (Int.ofNat (getTickSourceLogRShifted63Nat I)))
      (.int (Int.ofNat 128)) = .ok (getTickSourceLogF63Value I)
  rw [evalBinaryOp_int_shr_ok]
  · unfold getTickSourceLogF63Value getTickSourceLogF63Nat
    rw [intOfNat_toNat_div_pow_cast]
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_lt.mpr (getTickSourceLogRShifted63Nat_lt_wordModulus I)
  · norm_num
  · norm_num

theorem getTickStoreAfterLogF63Let_r (I : ExecutionEnv) :
    (getTickStoreAfterLogF63Let I).get? "r" =
      some (getTickSourceLogRShifted63Value I) := by
  rw [getTickStoreAfterLogF63Let]
  rw [store_get_ne (getTickStoreAfterLogRShifted63 I) (k := "f") (a := "r")
    (getTickSourceLogF63Value I) (by decide)]
  exact getTickStoreAfterLogRShifted63_r I

theorem getTickStoreAfterLogF63Let_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogF63Let I).get? "log_2" =
      some (getTickSourceLog2BaseValue I) := by
  rw [getTickStoreAfterLogF63Let]
  rw [store_get_ne (getTickStoreAfterLogRShifted63 I) (k := "f") (a := "log_2")
    (getTickSourceLogF63Value I) (by decide)]
  exact getTickStoreAfterLogRShifted63_log2 I

theorem getTickStoreAfterLogF63Let_f (I : ExecutionEnv) :
    (getTickStoreAfterLogF63Let I).get? "f" = some (getTickSourceLogF63Value I) := by
  rw [getTickStoreAfterLogF63Let, store_get_self]

theorem evalExpr_getTick_log2Var_afterLogF63 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogF63Let I }
      evm (.var "log_2") = .ok (getTickSourceLog2BaseValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterLogF63Let_log2]

theorem evalExpr_getTick_fVar_afterLogF63 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogF63Let I }
      evm (.var "f") = .ok (getTickSourceLogF63Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterLogF63Let_f]

theorem evalExpr_getTick_log2_add_f63 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogF63Let I }
      evm (addE (.var "log_2") (mulE (.var "f") (.intLit (2 ^ (63 : Nat))))) =
      .ok (getTickSourceLog2After63Value I) := by
  unfold addE mulE getTickSourceLog2After63Value getTickSourceLog2After63Int
  simp only [evalExpr?, evalExpr_getTick_log2Var_afterLogF63, evalExpr_getTick_fVar_afterLogF63,
    EvalResult.bind, bind, evalBinaryOp?, getTickSourceLogF63Value,
    getTickSourceLog2BaseValue]

theorem assignStorageRef_getTick_log2_after63 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterLogF63Let I }
      evm .localVar (varRef "log_2") (getTickSourceLog2After63Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterLog2Step63 I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterLogF63Let_log2]
  simp [getTickStoreAfterLog2Step63, updateLocalPath?, pure, bind, EvalResult.bind]

theorem getTickStoreAfterLog2Step63_r (I : ExecutionEnv) :
    (getTickStoreAfterLog2Step63 I).get? "r" =
      some (getTickSourceLogRShifted63Value I) := by
  rw [getTickStoreAfterLog2Step63]
  rw [store_get_ne (getTickStoreAfterLogF63Let I) (k := "log_2") (a := "r")
    (getTickSourceLog2After63Value I) (by decide)]
  exact getTickStoreAfterLogF63Let_r I

theorem getTickStoreAfterLog2Step63_f (I : ExecutionEnv) :
    (getTickStoreAfterLog2Step63 I).get? "f" = some (getTickSourceLogF63Value I) := by
  rw [getTickStoreAfterLog2Step63]
  rw [store_get_ne (getTickStoreAfterLogF63Let I) (k := "log_2") (a := "f")
    (getTickSourceLog2After63Value I) (by decide)]
  exact getTickStoreAfterLogF63Let_f I

theorem evalExpr_getTick_rVar_afterLog2Step63 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLog2Step63 I }
      evm (.var "r") = .ok (getTickSourceLogRShifted63Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterLog2Step63_r]

theorem evalExpr_getTick_fVar_afterLog2Step63 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLog2Step63 I }
      evm (.var "f") = .ok (getTickSourceLogF63Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterLog2Step63_f]

theorem evalExpr_getTick_log_r_after63 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLog2Step63 I }
      evm (shrE (.var "r") (.var "f")) = .ok (getTickSourceLogRAfter63Value I) := by
  unfold shrE
  simp only [evalExpr?, evalExpr_getTick_rVar_afterLog2Step63,
    evalExpr_getTick_fVar_afterLog2Step63, EvalResult.bind, bind]
  change evalBinaryOp? .shr (.int (Int.ofNat (getTickSourceLogRShifted63Nat I)))
      (.int (Int.ofNat (getTickSourceLogF63Nat I))) =
    .ok (getTickSourceLogRAfter63Value I)
  rw [evalBinaryOp_int_shr_ok]
  · unfold getTickSourceLogRAfter63Value getTickSourceLogRAfter63Nat
    rw [intOfNat_toNat_div_pow_cast]
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_lt.mpr (getTickSourceLogRShifted63Nat_lt_wordModulus I)
  · exact Int.natCast_nonneg _
  · have hle := getTickSourceLogF63Nat_le_1 I
    have hlt : getTickSourceLogF63Nat I < 256 := by omega
    exact Int.ofNat_lt.mpr hlt

theorem assignStorageRef_getTick_r_afterLog63 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterLog2Step63 I }
      evm .localVar (varRef "r") (getTickSourceLogRAfter63Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterLogStep63 I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterLog2Step63_r]
  simp [getTickStoreAfterLogStep63, updateLocalPath?, pure, bind, EvalResult.bind]

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogStep63 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLog2BaseLet I }
      evm (logStep 63 true)
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep63 I } evm) := by
  change ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLog2BaseLet I }
      evm
      [ .assign .localVar (varRef "r") (shrE (mulE (.var "r") (.var "r")) (.intLit 127)),
        .letDecl "f" (some uint256) (shrE (.var "r") shift128),
        .assign .localVar (varRef "log_2")
          (addE (.var "log_2") (mulE (.var "f") (.intLit (2 ^ (63 : Nat))))),
        .assign .localVar (varRef "r") (shrE (.var "r") (.var "f")) ]
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep63 I } evm)
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_log_r_shifted_63 evm I)
      (assignStorageRef_getTick_r_shifted63 evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_getTick_log_f63 evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_log2_add_f63 evm I)
      (assignStorageRef_getTick_log2_after63 evm I)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_log_r_after63 evm I)
      (assignStorageRef_getTick_r_afterLog63 evm I))
    ExecBlock.nil

theorem uniswapV3PoolGetTickAtSqrtRatioSourceThroughLogStep63 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreWithMsb I } evm
      ((msbStep 7 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF ++
        msbStep 6 0xFFFFFFFFFFFFFFFF ++
        msbStep 5 0xFFFFFFFF ++
        msbStep 4 0xFFFF ++
        msbStep 3 0xFF ++
        msbStep 2 0xF ++
        msbStep 1 0x3 ++
        [ .letDecl "f" (some uint256)
            (.ite (gtE (.var "r") (.intLit 0x1)) (.intLit 1) (.intLit 0)),
          .assign .localVar (varRef "msb") (addE (.var "msb") (.var "f")),
          Stmt.ite (geE (.var "msb") (.intLit 128))
            [ .assign .localVar (varRef "r")
                (shrE (.var "ratio") (subE (.var "msb") (.intLit 127))) ]
            [ .assign .localVar (varRef "r")
                (shlE (.var "ratio") (subE (.intLit 127) (.var "msb"))) ],
          .letDecl "log_2" (some int256)
            (mulE (subE (.var "msb") (.intLit 128)) (.intLit (2 ^ (64 : Nat)))) ]) ++
        logStep 63 true)
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep63 I } evm) := by
  exact execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceThroughLog2Base evm I)
    (uniswapV3PoolGetTickAtSqrtRatioSourceLogStep63 evm I)

end Benchmarks.UniswapV3Pool

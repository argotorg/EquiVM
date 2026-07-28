import Benchmarks.UniswapV3Pool.InitializeSourceGetTickLog

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

theorem sourceLogStepNextNat_lt_twoPow128 (s : Nat) (hs : s < 2 ^ (129 : Nat)) :
    s / 2 ^ (s / 2 ^ (128 : Nat)) < 2 ^ (128 : Nat) := by
  have hf_lt : s / 2 ^ (128 : Nat) < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ (128 : Nat))]
    norm_num
    exact hs
  have hf_le : s / 2 ^ (128 : Nat) ≤ 1 := by omega
  by_cases hf0 : s / 2 ^ (128 : Nat) = 0
  · have hs_lt : s < 2 ^ (128 : Nat) := by
      have hzero := Nat.div_eq_zero_iff.mp hf0
      omega
    rw [hf0]
    simpa using hs_lt
  · have hf1 : s / 2 ^ (128 : Nat) = 1 := by omega
    rw [hf1]
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ (1 : Nat))]
    norm_num
    exact hs

theorem getTickSourceLogRAfter63Nat_lt_twoPow128 (I : ExecutionEnv) :
    getTickSourceLogRAfter63Nat I < 2 ^ (128 : Nat) := by
  unfold getTickSourceLogRAfter63Nat getTickSourceLogF63Nat
  exact sourceLogStepNextNat_lt_twoPow128
    (getTickSourceLogRShifted63Nat I) (getTickSourceLogRShifted63Nat_lt_twoPow129 I)

theorem getTickSourceLogRAfter63Nat_mul_self_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceLogRAfter63Nat I * getTickSourceLogRAfter63Nat I < EVM.wordModulus := by
  have hr := getTickSourceLogRAfter63Nat_lt_twoPow128 I
  have hrle : getTickSourceLogRAfter63Nat I ≤ 2 ^ (128 : Nat) - 1 :=
    Nat.le_pred_of_lt hr
  have hmul := Nat.mul_le_mul hrle hrle
  exact Nat.lt_of_le_of_lt hmul (by norm_num [EVM.wordModulus, EVM.twoPow])

def getTickSourceLogRShifted62Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogRAfter63Nat I * getTickSourceLogRAfter63Nat I / 2 ^ (127 : Nat)

def getTickSourceLogRShifted62Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceLogRShifted62Nat I)

def getTickStoreAfterLogRShifted62 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterLogStep63 I).insert "r" (getTickSourceLogRShifted62Value I)

def getTickSourceLogF62Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogRShifted62Nat I / 2 ^ (128 : Nat)

def getTickSourceLogF62Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceLogF62Nat I)

def getTickStoreAfterLogF62Let (I : ExecutionEnv) : Store :=
  (getTickStoreAfterLogRShifted62 I).insert "f" (getTickSourceLogF62Value I)

def getTickSourceLog2After62Int (I : ExecutionEnv) : Int :=
  getTickSourceLog2After63Int I + (getTickSourceLogF62Nat I : Int) * (2 ^ (62 : Nat) : Int)

def getTickSourceLog2After62Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceLog2After62Int I)

def getTickStoreAfterLog2Step62 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterLogF62Let I).insert "log_2" (getTickSourceLog2After62Value I)

def getTickSourceLogRAfter62Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogRShifted62Nat I / 2 ^ getTickSourceLogF62Nat I

def getTickSourceLogRAfter62Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceLogRAfter62Nat I)

def getTickStoreAfterLogStep62 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterLog2Step62 I).insert "r" (getTickSourceLogRAfter62Value I)

theorem getTickSourceLogRShifted62Nat_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceLogRShifted62Nat I < EVM.wordModulus := by
  unfold getTickSourceLogRShifted62Nat
  exact lt_of_le_of_lt (Nat.div_le_self _ _)
    (getTickSourceLogRAfter63Nat_mul_self_lt_wordModulus I)

theorem getTickSourceLogRShifted62Nat_lt_twoPow129 (I : ExecutionEnv) :
    getTickSourceLogRShifted62Nat I < 2 ^ (129 : Nat) := by
  unfold getTickSourceLogRShifted62Nat
  rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ (127 : Nat))]
  rw [← Nat.pow_add]
  norm_num
  exact getTickSourceLogRAfter63Nat_mul_self_lt_wordModulus I

theorem getTickSourceLogF62Nat_le_1 (I : ExecutionEnv) :
    getTickSourceLogF62Nat I ≤ 1 := by
  unfold getTickSourceLogF62Nat
  have hshifted := getTickSourceLogRShifted62Nat_lt_twoPow129 I
  have hf : getTickSourceLogRShifted62Nat I / 2 ^ (128 : Nat) < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ (128 : Nat))]
    norm_num
    exact hshifted
  omega

theorem getTickSourceLogRAfter62Nat_lt_twoPow128 (I : ExecutionEnv) :
    getTickSourceLogRAfter62Nat I < 2 ^ (128 : Nat) := by
  unfold getTickSourceLogRAfter62Nat getTickSourceLogF62Nat
  exact sourceLogStepNextNat_lt_twoPow128
    (getTickSourceLogRShifted62Nat I) (getTickSourceLogRShifted62Nat_lt_twoPow129 I)

theorem getTickSourceLogRAfter62Nat_mul_self_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceLogRAfter62Nat I * getTickSourceLogRAfter62Nat I < EVM.wordModulus := by
  have hr := getTickSourceLogRAfter62Nat_lt_twoPow128 I
  have hrle : getTickSourceLogRAfter62Nat I ≤ 2 ^ (128 : Nat) - 1 :=
    Nat.le_pred_of_lt hr
  have hmul := Nat.mul_le_mul hrle hrle
  exact Nat.lt_of_le_of_lt hmul (by norm_num [EVM.wordModulus, EVM.twoPow])

theorem getTickStoreAfterLog2Step63_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLog2Step63 I).get? "log_2" =
      some (getTickSourceLog2After63Value I) := by
  rw [getTickStoreAfterLog2Step63, store_get_self]

theorem getTickStoreAfterLogStep63_r (I : ExecutionEnv) :
    (getTickStoreAfterLogStep63 I).get? "r" = some (getTickSourceLogRAfter63Value I) := by
  rw [getTickStoreAfterLogStep63, store_get_self]

theorem getTickStoreAfterLogStep63_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogStep63 I).get? "log_2" =
      some (getTickSourceLog2After63Value I) := by
  rw [getTickStoreAfterLogStep63]
  rw [store_get_ne (getTickStoreAfterLog2Step63 I) (k := "r") (a := "log_2")
    (getTickSourceLogRAfter63Value I) (by decide)]
  exact getTickStoreAfterLog2Step63_log2 I

theorem evalExpr_getTick_rVar_afterLogStep63 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogStep63 I }
      evm (.var "r") = .ok (getTickSourceLogRAfter63Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterLogStep63_r]

theorem evalExpr_getTick_log2Var_afterLogStep63 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogStep63 I }
      evm (.var "log_2") = .ok (getTickSourceLog2After63Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterLogStep63_log2]

theorem evalExpr_getTick_log_r_mul_r_62 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogStep63 I }
      evm (mulE (.var "r") (.var "r")) =
      .ok (.int (Int.ofNat (getTickSourceLogRAfter63Nat I * getTickSourceLogRAfter63Nat I))) := by
  unfold mulE
  simp only [evalExpr?, evalExpr_getTick_rVar_afterLogStep63, EvalResult.bind, bind,
    evalBinaryOp?, getTickSourceLogRAfter63Value]
  rw [← Int.natCast_mul]
  rfl

theorem evalExpr_getTick_log_r_shifted_62 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogStep63 I }
      evm (shrE (mulE (.var "r") (.var "r")) (.intLit 127)) =
      .ok (getTickSourceLogRShifted62Value I) := by
  unfold shrE
  simp only [evalExpr?, evalExpr_getTick_log_r_mul_r_62, EvalResult.bind, bind, pure]
  rw [evalBinaryOp_int_shr_ok]
  · rw [getTickSourceLogRShifted62Value, getTickSourceLogRShifted62Nat]
    rw [intOfNat_toNat_div_pow_127_cast]
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_lt.mpr (getTickSourceLogRAfter63Nat_mul_self_lt_wordModulus I)
  · norm_num
  · norm_num

theorem assignStorageRef_getTick_r_shifted62 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterLogStep63 I }
      evm .localVar (varRef "r") (getTickSourceLogRShifted62Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterLogRShifted62 I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterLogStep63_r]
  simp [getTickStoreAfterLogRShifted62, updateLocalPath?, pure, bind, EvalResult.bind]

theorem getTickStoreAfterLogRShifted62_r (I : ExecutionEnv) :
    (getTickStoreAfterLogRShifted62 I).get? "r" =
      some (getTickSourceLogRShifted62Value I) := by
  rw [getTickStoreAfterLogRShifted62, store_get_self]

theorem getTickStoreAfterLogRShifted62_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogRShifted62 I).get? "log_2" =
      some (getTickSourceLog2After63Value I) := by
  rw [getTickStoreAfterLogRShifted62]
  rw [store_get_ne (getTickStoreAfterLogStep63 I) (k := "r") (a := "log_2")
    (getTickSourceLogRShifted62Value I) (by decide)]
  exact getTickStoreAfterLogStep63_log2 I

theorem evalExpr_getTick_rVar_afterLogRShifted62 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogRShifted62 I }
      evm (.var "r") = .ok (getTickSourceLogRShifted62Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterLogRShifted62_r]

theorem evalExpr_getTick_log_f62 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogRShifted62 I }
      evm (shrE (.var "r") shift128) = .ok (getTickSourceLogF62Value I) := by
  unfold shrE shift128
  simp only [evalExpr?, evalExpr_getTick_rVar_afterLogRShifted62, EvalResult.bind, bind, pure]
  change evalBinaryOp? .shr (.int (Int.ofNat (getTickSourceLogRShifted62Nat I)))
      (.int (Int.ofNat 128)) = .ok (getTickSourceLogF62Value I)
  rw [evalBinaryOp_int_shr_ok]
  · unfold getTickSourceLogF62Value getTickSourceLogF62Nat
    rw [intOfNat_toNat_div_pow_cast]
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_lt.mpr (getTickSourceLogRShifted62Nat_lt_wordModulus I)
  · norm_num
  · norm_num

theorem getTickStoreAfterLogF62Let_r (I : ExecutionEnv) :
    (getTickStoreAfterLogF62Let I).get? "r" =
      some (getTickSourceLogRShifted62Value I) := by
  rw [getTickStoreAfterLogF62Let]
  rw [store_get_ne (getTickStoreAfterLogRShifted62 I) (k := "f") (a := "r")
    (getTickSourceLogF62Value I) (by decide)]
  exact getTickStoreAfterLogRShifted62_r I

theorem getTickStoreAfterLogF62Let_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogF62Let I).get? "log_2" =
      some (getTickSourceLog2After63Value I) := by
  rw [getTickStoreAfterLogF62Let]
  rw [store_get_ne (getTickStoreAfterLogRShifted62 I) (k := "f") (a := "log_2")
    (getTickSourceLogF62Value I) (by decide)]
  exact getTickStoreAfterLogRShifted62_log2 I

theorem getTickStoreAfterLogF62Let_f (I : ExecutionEnv) :
    (getTickStoreAfterLogF62Let I).get? "f" = some (getTickSourceLogF62Value I) := by
  rw [getTickStoreAfterLogF62Let, store_get_self]

theorem evalExpr_getTick_log2Var_afterLogF62 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogF62Let I }
      evm (.var "log_2") = .ok (getTickSourceLog2After63Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterLogF62Let_log2]

theorem evalExpr_getTick_fVar_afterLogF62 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogF62Let I }
      evm (.var "f") = .ok (getTickSourceLogF62Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterLogF62Let_f]

theorem evalExpr_getTick_log2_add_f62 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogF62Let I }
      evm (addE (.var "log_2") (mulE (.var "f") (.intLit (2 ^ (62 : Nat))))) =
      .ok (getTickSourceLog2After62Value I) := by
  unfold addE mulE getTickSourceLog2After62Value getTickSourceLog2After62Int
  simp only [evalExpr?, evalExpr_getTick_log2Var_afterLogF62, evalExpr_getTick_fVar_afterLogF62,
    EvalResult.bind, bind, evalBinaryOp?, getTickSourceLogF62Value,
    getTickSourceLog2After63Value]

theorem assignStorageRef_getTick_log2_after62 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterLogF62Let I }
      evm .localVar (varRef "log_2") (getTickSourceLog2After62Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterLog2Step62 I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterLogF62Let_log2]
  simp [getTickStoreAfterLog2Step62, updateLocalPath?, pure, bind, EvalResult.bind]

theorem getTickStoreAfterLog2Step62_r (I : ExecutionEnv) :
    (getTickStoreAfterLog2Step62 I).get? "r" =
      some (getTickSourceLogRShifted62Value I) := by
  rw [getTickStoreAfterLog2Step62]
  rw [store_get_ne (getTickStoreAfterLogF62Let I) (k := "log_2") (a := "r")
    (getTickSourceLog2After62Value I) (by decide)]
  exact getTickStoreAfterLogF62Let_r I

theorem getTickStoreAfterLog2Step62_f (I : ExecutionEnv) :
    (getTickStoreAfterLog2Step62 I).get? "f" = some (getTickSourceLogF62Value I) := by
  rw [getTickStoreAfterLog2Step62]
  rw [store_get_ne (getTickStoreAfterLogF62Let I) (k := "log_2") (a := "f")
    (getTickSourceLog2After62Value I) (by decide)]
  exact getTickStoreAfterLogF62Let_f I

theorem evalExpr_getTick_rVar_afterLog2Step62 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLog2Step62 I }
      evm (.var "r") = .ok (getTickSourceLogRShifted62Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterLog2Step62_r]

theorem evalExpr_getTick_fVar_afterLog2Step62 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLog2Step62 I }
      evm (.var "f") = .ok (getTickSourceLogF62Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterLog2Step62_f]

theorem evalExpr_getTick_log_r_after62 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLog2Step62 I }
      evm (shrE (.var "r") (.var "f")) = .ok (getTickSourceLogRAfter62Value I) := by
  unfold shrE
  simp only [evalExpr?, evalExpr_getTick_rVar_afterLog2Step62,
    evalExpr_getTick_fVar_afterLog2Step62, EvalResult.bind, bind]
  change evalBinaryOp? .shr (.int (Int.ofNat (getTickSourceLogRShifted62Nat I)))
      (.int (Int.ofNat (getTickSourceLogF62Nat I))) =
    .ok (getTickSourceLogRAfter62Value I)
  rw [evalBinaryOp_int_shr_ok]
  · unfold getTickSourceLogRAfter62Value getTickSourceLogRAfter62Nat
    rw [intOfNat_toNat_div_pow_cast]
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_lt.mpr (getTickSourceLogRShifted62Nat_lt_wordModulus I)
  · exact Int.natCast_nonneg _
  · have hle := getTickSourceLogF62Nat_le_1 I
    have hlt : getTickSourceLogF62Nat I < 256 := by omega
    exact Int.ofNat_lt.mpr hlt

theorem assignStorageRef_getTick_r_afterLog62 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterLog2Step62 I }
      evm .localVar (varRef "r") (getTickSourceLogRAfter62Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterLogStep62 I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterLog2Step62_r]
  simp [getTickStoreAfterLogStep62, updateLocalPath?, pure, bind, EvalResult.bind]

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogStep62 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep63 I }
      evm (logStep 62 true)
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep62 I } evm) := by
  change ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep63 I }
      evm
      [ .assign .localVar (varRef "r") (shrE (mulE (.var "r") (.var "r")) (.intLit 127)),
        .letDecl "f" (some uint256) (shrE (.var "r") shift128),
        .assign .localVar (varRef "log_2")
          (addE (.var "log_2") (mulE (.var "f") (.intLit (2 ^ (62 : Nat))))),
        .assign .localVar (varRef "r") (shrE (.var "r") (.var "f")) ]
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep62 I } evm)
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_log_r_shifted_62 evm I)
      (assignStorageRef_getTick_r_shifted62 evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_getTick_log_f62 evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_log2_add_f62 evm I)
      (assignStorageRef_getTick_log2_after62 evm I)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_log_r_after62 evm I)
      (assignStorageRef_getTick_r_afterLog62 evm I))
    ExecBlock.nil

theorem uniswapV3PoolGetTickAtSqrtRatioSourceThroughLogStep62 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreWithMsb I } evm
      (((msbStep 7 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF ++
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
        logStep 63 true) ++
        logStep 62 true)
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep62 I } evm) := by
  exact execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceThroughLogStep63 evm I)
    (uniswapV3PoolGetTickAtSqrtRatioSourceLogStep62 evm I)

end Benchmarks.UniswapV3Pool

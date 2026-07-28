import Benchmarks.UniswapV3Pool.InitializeSourceSuccess

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

def getTickSourceRAfterMsb5Gt4 (I : ExecutionEnv) : Bool :=
  decide (getTickSourceRAfterMsb5Nat I > 0xFFFF)

def getTickSourceMsbF4Nat (I : ExecutionEnv) : Nat :=
  if getTickSourceRAfterMsb5Gt4 I then 2 ^ (4 : Nat) else 0

def getTickSourceMsbF4Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceMsbF4Nat I)

def getTickStoreAfterF4Let (I : ExecutionEnv) : Store :=
  (getTickStoreAfterMsbStep5 I).insert "f" (getTickSourceMsbF4Value I)

def getTickSourceMsbAfter4Nat (I : ExecutionEnv) : Nat :=
  getTickSourceMsbAfter5Nat I + getTickSourceMsbF4Nat I

def getTickSourceMsbAfter4Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceMsbAfter4Nat I)

def getTickStoreAfterMsb4 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterF4Let I).insert "msb" (getTickSourceMsbAfter4Value I)

def getTickSourceRAfterMsb4Nat (I : ExecutionEnv) : Nat :=
  getTickSourceRAfterMsb5Nat I / 2 ^ getTickSourceMsbF4Nat I

def getTickSourceRAfterMsb4Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceRAfterMsb4Nat I)

def getTickStoreAfterMsbStep4 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterMsb4 I).insert "r" (getTickSourceRAfterMsb4Value I)

theorem getTickSourceRAfterMsb5Nat_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceRAfterMsb5Nat I < EVM.wordModulus := by
  unfold getTickSourceRAfterMsb5Nat
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (getTickSourceRAfterMsb6Nat_lt_wordModulus I)

theorem getTickStoreAfterMsb5_msb (I : ExecutionEnv) :
    (getTickStoreAfterMsb5 I).get? "msb" = some (getTickSourceMsbAfter5Value I) := by
  rw [getTickStoreAfterMsb5, store_get_self]

theorem getTickStoreAfterMsbStep5_r (I : ExecutionEnv) :
    (getTickStoreAfterMsbStep5 I).get? "r" =
      some (getTickSourceRAfterMsb5Value I) := by
  rw [getTickStoreAfterMsbStep5, store_get_self]

theorem getTickStoreAfterMsbStep5_msb (I : ExecutionEnv) :
    (getTickStoreAfterMsbStep5 I).get? "msb" =
      some (getTickSourceMsbAfter5Value I) := by
  rw [getTickStoreAfterMsbStep5]
  rw [store_get_ne (getTickStoreAfterMsb5 I) (k := "r") (a := "msb")
    (getTickSourceRAfterMsb5Value I) (by decide)]
  exact getTickStoreAfterMsb5_msb I

theorem evalExpr_getTick_rVar_afterMsbStep5 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbStep5 I }
      evm (.var "r") = .ok (getTickSourceRAfterMsb5Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsbStep5_r]

theorem evalExpr_getTick_msbVar_afterMsbStep5 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbStep5 I }
      evm (.var "msb") = .ok (getTickSourceMsbAfter5Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsbStep5_msb]

theorem evalBinaryOp_getTick_rAfter5Gt4 (I : ExecutionEnv) :
    evalBinaryOp? .gt (getTickSourceRAfterMsb5Value I)
      (.int 0xFFFF) =
    .ok (.bool (getTickSourceRAfterMsb5Gt4 I)) := by
  unfold getTickSourceRAfterMsb5Value getTickSourceRAfterMsb5Gt4
  simp only [evalBinaryOp?]
  by_cases h : getTickSourceRAfterMsb5Nat I > 0xFFFF
  · have hInt : ((getTickSourceRAfterMsb5Nat I : Nat) : Int) > (0xFFFF : Int) := by
      omega
    rw [decide_eq_true hInt, decide_eq_true h]
  · have hInt : ¬(((getTickSourceRAfterMsb5Nat I : Nat) : Int) > (0xFFFF : Int)) := by
      omega
    rw [decide_eq_false hInt, decide_eq_false h]

theorem evalExpr_getTick_msbF4 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbStep5 I } evm
      (.ite (gtE (.var "r") (.intLit 0xFFFF))
        (.intLit (2 ^ (4 : Nat))) (.intLit 0)) =
      .ok (getTickSourceMsbF4Value I) := by
  unfold gtE getTickSourceMsbF4Value getTickSourceMsbF4Nat
  simp only [evalExpr?, evalExpr_getTick_rVar_afterMsbStep5, EvalResult.bind, bind, pure]
  rw [evalBinaryOp_getTick_rAfter5Gt4]
  cases getTickSourceRAfterMsb5Gt4 I <;> rfl

theorem getTickSourceMsbF4Nat_le_16 (I : ExecutionEnv) :
    getTickSourceMsbF4Nat I ≤ 16 := by
  unfold getTickSourceMsbF4Nat
  split <;> norm_num

theorem getTickStoreAfterF4Let_msb (I : ExecutionEnv) :
    (getTickStoreAfterF4Let I).get? "msb" = some (getTickSourceMsbAfter5Value I) := by
  rw [getTickStoreAfterF4Let]
  rw [store_get_ne (getTickStoreAfterMsbStep5 I) (k := "f") (a := "msb")
    (getTickSourceMsbF4Value I) (by decide)]
  exact getTickStoreAfterMsbStep5_msb I

theorem getTickStoreAfterF4Let_f (I : ExecutionEnv) :
    (getTickStoreAfterF4Let I).get? "f" = some (getTickSourceMsbF4Value I) := by
  rw [getTickStoreAfterF4Let, store_get_self]

theorem evalExpr_getTick_msb_add_f4 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterF4Let I } evm
      (addE (.var "msb") (.var "f")) = .ok (getTickSourceMsbAfter4Value I) := by
  unfold addE getTickSourceMsbAfter4Value getTickSourceMsbAfter4Nat
  simp only [evalExpr?, EvalResult.ofOption, getTickStoreAfterF4Let_msb,
    getTickStoreAfterF4Let_f, getTickSourceMsbAfter5Value, getTickSourceMsbF4Value,
    EvalResult.bind, bind, evalBinaryOp?]
  rw [(Nat.cast_add (getTickSourceMsbAfter5Nat I) (getTickSourceMsbF4Nat I)).symm]

theorem assignStorageRef_getTick_msb_afterF4 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterF4Let I }
      evm .localVar (varRef "msb") (getTickSourceMsbAfter4Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterMsb4 I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterF4Let_msb]
  simp [getTickStoreAfterMsb4, updateLocalPath?, pure, bind, EvalResult.bind]

theorem getTickStoreAfterMsb4_r (I : ExecutionEnv) :
    (getTickStoreAfterMsb4 I).get? "r" = some (getTickSourceRAfterMsb5Value I) := by
  rw [getTickStoreAfterMsb4]
  rw [store_get_ne (getTickStoreAfterF4Let I) (k := "msb") (a := "r")
    (getTickSourceMsbAfter4Value I) (by decide)]
  rw [getTickStoreAfterF4Let]
  rw [store_get_ne (getTickStoreAfterMsbStep5 I) (k := "f") (a := "r")
    (getTickSourceMsbF4Value I) (by decide)]
  exact getTickStoreAfterMsbStep5_r I

theorem getTickStoreAfterMsb4_f (I : ExecutionEnv) :
    (getTickStoreAfterMsb4 I).get? "f" = some (getTickSourceMsbF4Value I) := by
  rw [getTickStoreAfterMsb4]
  rw [store_get_ne (getTickStoreAfterF4Let I) (k := "msb") (a := "f")
    (getTickSourceMsbAfter4Value I) (by decide)]
  exact getTickStoreAfterF4Let_f I

theorem evalExpr_getTick_rVar_afterMsb4 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb4 I }
      evm (.var "r") = .ok (getTickSourceRAfterMsb5Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsb4_r]

theorem evalExpr_getTick_fVar_afterMsb4 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb4 I }
      evm (.var "f") = .ok (getTickSourceMsbF4Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsb4_f]

theorem evalExpr_getTick_r_shr_f4 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb4 I } evm
      (shrE (.var "r") (.var "f")) = .ok (getTickSourceRAfterMsb4Value I) := by
  unfold shrE
  simp only [evalExpr?, evalExpr_getTick_rVar_afterMsb4,
    evalExpr_getTick_fVar_afterMsb4, EvalResult.bind, bind]
  change evalBinaryOp? .shr (.int (Int.ofNat (getTickSourceRAfterMsb5Nat I)))
      (.int (Int.ofNat (getTickSourceMsbF4Nat I))) =
    .ok (getTickSourceRAfterMsb4Value I)
  rw [evalBinaryOp_int_shr_ok]
  · unfold getTickSourceRAfterMsb4Value getTickSourceRAfterMsb4Nat
    rw [intOfNat_toNat_div_pow_cast]
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_lt.mpr (getTickSourceRAfterMsb5Nat_lt_wordModulus I)
  · exact Int.natCast_nonneg _
  · have hle := getTickSourceMsbF4Nat_le_16 I
    have hltNat : getTickSourceMsbF4Nat I < 256 := by omega
    exact Int.ofNat_lt.mpr hltNat

theorem assignStorageRef_getTick_r_afterF4 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterMsb4 I }
      evm .localVar (varRef "r") (getTickSourceRAfterMsb4Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterMsbStep4 I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterMsb4_r]
  simp [getTickStoreAfterMsbStep4, updateLocalPath?, pure, bind, EvalResult.bind]

theorem uniswapV3PoolGetTickAtSqrtRatioSourceMsbStep4 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterMsbStep5 I } evm
      (msbStep 4 0xFFFF)
      (.ok { contract := contract v, locals := getTickStoreAfterMsbStep4 I } evm) := by
  change ExecBlock (config v)
      { contract := contract v, locals := getTickStoreAfterMsbStep5 I } evm
      [ .letDecl "f" (some uint256)
          (.ite (gtE (.var "r") (.intLit 0xFFFF))
            (.intLit (2 ^ (4 : Nat))) (.intLit 0)),
        .assign .localVar (varRef "msb") (addE (.var "msb") (.var "f")),
        .assign .localVar (varRef "r") (shrE (.var "r") (.var "f")) ]
      (.ok { contract := contract v, locals := getTickStoreAfterMsbStep4 I } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_getTick_msbF4 evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_msb_add_f4 evm I)
      (assignStorageRef_getTick_msb_afterF4 evm I)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_r_shr_f4 evm I)
      (assignStorageRef_getTick_r_afterF4 evm I))
    ExecBlock.nil

theorem uniswapV3PoolGetTickAtSqrtRatioSourceMsbSteps7654 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreWithMsb I } evm
      (msbStep 7 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF ++
        msbStep 6 0xFFFFFFFFFFFFFFFF ++
        msbStep 5 0xFFFFFFFF ++
        msbStep 4 0xFFFF)
      (.ok { contract := contract v, locals := getTickStoreAfterMsbStep4 I } evm) := by
  exact execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceMsbSteps765 evm I)
    (uniswapV3PoolGetTickAtSqrtRatioSourceMsbStep4 evm I)

def getTickSourceRAfterMsb4Gt3 (I : ExecutionEnv) : Bool :=
  decide (getTickSourceRAfterMsb4Nat I > 0xFF)

def getTickSourceMsbF3Nat (I : ExecutionEnv) : Nat :=
  if getTickSourceRAfterMsb4Gt3 I then 2 ^ (3 : Nat) else 0

def getTickSourceMsbF3Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceMsbF3Nat I)

def getTickStoreAfterF3Let (I : ExecutionEnv) : Store :=
  (getTickStoreAfterMsbStep4 I).insert "f" (getTickSourceMsbF3Value I)

def getTickSourceMsbAfter3Nat (I : ExecutionEnv) : Nat :=
  getTickSourceMsbAfter4Nat I + getTickSourceMsbF3Nat I

def getTickSourceMsbAfter3Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceMsbAfter3Nat I)

def getTickStoreAfterMsb3 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterF3Let I).insert "msb" (getTickSourceMsbAfter3Value I)

def getTickSourceRAfterMsb3Nat (I : ExecutionEnv) : Nat :=
  getTickSourceRAfterMsb4Nat I / 2 ^ getTickSourceMsbF3Nat I

def getTickSourceRAfterMsb3Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceRAfterMsb3Nat I)

def getTickStoreAfterMsbStep3 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterMsb3 I).insert "r" (getTickSourceRAfterMsb3Value I)

theorem getTickSourceRAfterMsb4Nat_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceRAfterMsb4Nat I < EVM.wordModulus := by
  unfold getTickSourceRAfterMsb4Nat
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (getTickSourceRAfterMsb5Nat_lt_wordModulus I)

theorem getTickStoreAfterMsb4_msb (I : ExecutionEnv) :
    (getTickStoreAfterMsb4 I).get? "msb" = some (getTickSourceMsbAfter4Value I) := by
  rw [getTickStoreAfterMsb4, store_get_self]

theorem getTickStoreAfterMsbStep4_r (I : ExecutionEnv) :
    (getTickStoreAfterMsbStep4 I).get? "r" =
      some (getTickSourceRAfterMsb4Value I) := by
  rw [getTickStoreAfterMsbStep4, store_get_self]

theorem getTickStoreAfterMsbStep4_msb (I : ExecutionEnv) :
    (getTickStoreAfterMsbStep4 I).get? "msb" =
      some (getTickSourceMsbAfter4Value I) := by
  rw [getTickStoreAfterMsbStep4]
  rw [store_get_ne (getTickStoreAfterMsb4 I) (k := "r") (a := "msb")
    (getTickSourceRAfterMsb4Value I) (by decide)]
  exact getTickStoreAfterMsb4_msb I

theorem evalExpr_getTick_rVar_afterMsbStep4 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbStep4 I }
      evm (.var "r") = .ok (getTickSourceRAfterMsb4Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsbStep4_r]

theorem evalExpr_getTick_msbVar_afterMsbStep4 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbStep4 I }
      evm (.var "msb") = .ok (getTickSourceMsbAfter4Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsbStep4_msb]

theorem evalBinaryOp_getTick_rAfter4Gt3 (I : ExecutionEnv) :
    evalBinaryOp? .gt (getTickSourceRAfterMsb4Value I) (.int 0xFF) =
    .ok (.bool (getTickSourceRAfterMsb4Gt3 I)) := by
  unfold getTickSourceRAfterMsb4Value getTickSourceRAfterMsb4Gt3
  simp only [evalBinaryOp?]
  by_cases h : getTickSourceRAfterMsb4Nat I > 0xFF
  · have hInt : ((getTickSourceRAfterMsb4Nat I : Nat) : Int) > (0xFF : Int) := by
      omega
    rw [decide_eq_true hInt, decide_eq_true h]
  · have hInt : ¬(((getTickSourceRAfterMsb4Nat I : Nat) : Int) > (0xFF : Int)) := by
      omega
    rw [decide_eq_false hInt, decide_eq_false h]

theorem evalExpr_getTick_msbF3 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbStep4 I } evm
      (.ite (gtE (.var "r") (.intLit 0xFF))
        (.intLit (2 ^ (3 : Nat))) (.intLit 0)) =
      .ok (getTickSourceMsbF3Value I) := by
  unfold gtE getTickSourceMsbF3Value getTickSourceMsbF3Nat
  simp only [evalExpr?, evalExpr_getTick_rVar_afterMsbStep4, EvalResult.bind, bind, pure]
  rw [evalBinaryOp_getTick_rAfter4Gt3]
  cases getTickSourceRAfterMsb4Gt3 I <;> rfl

theorem getTickSourceMsbF3Nat_le_8 (I : ExecutionEnv) :
    getTickSourceMsbF3Nat I ≤ 8 := by
  unfold getTickSourceMsbF3Nat
  split <;> norm_num

theorem getTickStoreAfterF3Let_msb (I : ExecutionEnv) :
    (getTickStoreAfterF3Let I).get? "msb" = some (getTickSourceMsbAfter4Value I) := by
  rw [getTickStoreAfterF3Let]
  rw [store_get_ne (getTickStoreAfterMsbStep4 I) (k := "f") (a := "msb")
    (getTickSourceMsbF3Value I) (by decide)]
  exact getTickStoreAfterMsbStep4_msb I

theorem getTickStoreAfterF3Let_f (I : ExecutionEnv) :
    (getTickStoreAfterF3Let I).get? "f" = some (getTickSourceMsbF3Value I) := by
  rw [getTickStoreAfterF3Let, store_get_self]

theorem evalExpr_getTick_msb_add_f3 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterF3Let I } evm
      (addE (.var "msb") (.var "f")) = .ok (getTickSourceMsbAfter3Value I) := by
  unfold addE getTickSourceMsbAfter3Value getTickSourceMsbAfter3Nat
  simp only [evalExpr?, EvalResult.ofOption, getTickStoreAfterF3Let_msb,
    getTickStoreAfterF3Let_f, getTickSourceMsbAfter4Value, getTickSourceMsbF3Value,
    EvalResult.bind, bind, evalBinaryOp?]
  rw [(Nat.cast_add (getTickSourceMsbAfter4Nat I) (getTickSourceMsbF3Nat I)).symm]

theorem assignStorageRef_getTick_msb_afterF3 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterF3Let I }
      evm .localVar (varRef "msb") (getTickSourceMsbAfter3Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterMsb3 I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterF3Let_msb]
  simp [getTickStoreAfterMsb3, updateLocalPath?, pure, bind, EvalResult.bind]

theorem getTickStoreAfterMsb3_r (I : ExecutionEnv) :
    (getTickStoreAfterMsb3 I).get? "r" = some (getTickSourceRAfterMsb4Value I) := by
  rw [getTickStoreAfterMsb3]
  rw [store_get_ne (getTickStoreAfterF3Let I) (k := "msb") (a := "r")
    (getTickSourceMsbAfter3Value I) (by decide)]
  rw [getTickStoreAfterF3Let]
  rw [store_get_ne (getTickStoreAfterMsbStep4 I) (k := "f") (a := "r")
    (getTickSourceMsbF3Value I) (by decide)]
  exact getTickStoreAfterMsbStep4_r I

theorem getTickStoreAfterMsb3_f (I : ExecutionEnv) :
    (getTickStoreAfterMsb3 I).get? "f" = some (getTickSourceMsbF3Value I) := by
  rw [getTickStoreAfterMsb3]
  rw [store_get_ne (getTickStoreAfterF3Let I) (k := "msb") (a := "f")
    (getTickSourceMsbAfter3Value I) (by decide)]
  exact getTickStoreAfterF3Let_f I

theorem evalExpr_getTick_rVar_afterMsb3 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb3 I }
      evm (.var "r") = .ok (getTickSourceRAfterMsb4Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsb3_r]

theorem evalExpr_getTick_fVar_afterMsb3 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb3 I }
      evm (.var "f") = .ok (getTickSourceMsbF3Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsb3_f]

theorem evalExpr_getTick_r_shr_f3 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb3 I } evm
      (shrE (.var "r") (.var "f")) = .ok (getTickSourceRAfterMsb3Value I) := by
  unfold shrE
  simp only [evalExpr?, evalExpr_getTick_rVar_afterMsb3,
    evalExpr_getTick_fVar_afterMsb3, EvalResult.bind, bind]
  change evalBinaryOp? .shr (.int (Int.ofNat (getTickSourceRAfterMsb4Nat I)))
      (.int (Int.ofNat (getTickSourceMsbF3Nat I))) =
    .ok (getTickSourceRAfterMsb3Value I)
  rw [evalBinaryOp_int_shr_ok]
  · unfold getTickSourceRAfterMsb3Value getTickSourceRAfterMsb3Nat
    rw [intOfNat_toNat_div_pow_cast]
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_lt.mpr (getTickSourceRAfterMsb4Nat_lt_wordModulus I)
  · exact Int.natCast_nonneg _
  · have hle := getTickSourceMsbF3Nat_le_8 I
    have hltNat : getTickSourceMsbF3Nat I < 256 := by omega
    exact Int.ofNat_lt.mpr hltNat

theorem assignStorageRef_getTick_r_afterF3 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterMsb3 I }
      evm .localVar (varRef "r") (getTickSourceRAfterMsb3Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterMsbStep3 I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterMsb3_r]
  simp [getTickStoreAfterMsbStep3, updateLocalPath?, pure, bind, EvalResult.bind]

theorem uniswapV3PoolGetTickAtSqrtRatioSourceMsbStep3 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterMsbStep4 I } evm
      (msbStep 3 0xFF)
      (.ok { contract := contract v, locals := getTickStoreAfterMsbStep3 I } evm) := by
  change ExecBlock (config v)
      { contract := contract v, locals := getTickStoreAfterMsbStep4 I } evm
      [ .letDecl "f" (some uint256)
          (.ite (gtE (.var "r") (.intLit 0xFF))
            (.intLit (2 ^ (3 : Nat))) (.intLit 0)),
        .assign .localVar (varRef "msb") (addE (.var "msb") (.var "f")),
        .assign .localVar (varRef "r") (shrE (.var "r") (.var "f")) ]
      (.ok { contract := contract v, locals := getTickStoreAfterMsbStep3 I } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_getTick_msbF3 evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_msb_add_f3 evm I)
      (assignStorageRef_getTick_msb_afterF3 evm I)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_r_shr_f3 evm I)
      (assignStorageRef_getTick_r_afterF3 evm I))
    ExecBlock.nil

theorem uniswapV3PoolGetTickAtSqrtRatioSourceMsbSteps76543 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreWithMsb I } evm
      (msbStep 7 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF ++
        msbStep 6 0xFFFFFFFFFFFFFFFF ++
        msbStep 5 0xFFFFFFFF ++
        msbStep 4 0xFFFF ++
        msbStep 3 0xFF)
      (.ok { contract := contract v, locals := getTickStoreAfterMsbStep3 I } evm) := by
  exact execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceMsbSteps7654 evm I)
    (uniswapV3PoolGetTickAtSqrtRatioSourceMsbStep3 evm I)

def getTickSourceRAfterMsb3Gt2 (I : ExecutionEnv) : Bool :=
  decide (getTickSourceRAfterMsb3Nat I > 0xF)

def getTickSourceMsbF2Nat (I : ExecutionEnv) : Nat :=
  if getTickSourceRAfterMsb3Gt2 I then 2 ^ (2 : Nat) else 0

def getTickSourceMsbF2Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceMsbF2Nat I)

def getTickStoreAfterF2Let (I : ExecutionEnv) : Store :=
  (getTickStoreAfterMsbStep3 I).insert "f" (getTickSourceMsbF2Value I)

def getTickSourceMsbAfter2Nat (I : ExecutionEnv) : Nat :=
  getTickSourceMsbAfter3Nat I + getTickSourceMsbF2Nat I

def getTickSourceMsbAfter2Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceMsbAfter2Nat I)

def getTickStoreAfterMsb2 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterF2Let I).insert "msb" (getTickSourceMsbAfter2Value I)

def getTickSourceRAfterMsb2Nat (I : ExecutionEnv) : Nat :=
  getTickSourceRAfterMsb3Nat I / 2 ^ getTickSourceMsbF2Nat I

def getTickSourceRAfterMsb2Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceRAfterMsb2Nat I)

def getTickStoreAfterMsbStep2 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterMsb2 I).insert "r" (getTickSourceRAfterMsb2Value I)

theorem getTickSourceRAfterMsb3Nat_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceRAfterMsb3Nat I < EVM.wordModulus := by
  unfold getTickSourceRAfterMsb3Nat
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (getTickSourceRAfterMsb4Nat_lt_wordModulus I)

theorem getTickStoreAfterMsb3_msb (I : ExecutionEnv) :
    (getTickStoreAfterMsb3 I).get? "msb" = some (getTickSourceMsbAfter3Value I) := by
  rw [getTickStoreAfterMsb3, store_get_self]

theorem getTickStoreAfterMsbStep3_r (I : ExecutionEnv) :
    (getTickStoreAfterMsbStep3 I).get? "r" =
      some (getTickSourceRAfterMsb3Value I) := by
  rw [getTickStoreAfterMsbStep3, store_get_self]

theorem getTickStoreAfterMsbStep3_msb (I : ExecutionEnv) :
    (getTickStoreAfterMsbStep3 I).get? "msb" =
      some (getTickSourceMsbAfter3Value I) := by
  rw [getTickStoreAfterMsbStep3]
  rw [store_get_ne (getTickStoreAfterMsb3 I) (k := "r") (a := "msb")
    (getTickSourceRAfterMsb3Value I) (by decide)]
  exact getTickStoreAfterMsb3_msb I

theorem evalExpr_getTick_rVar_afterMsbStep3 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbStep3 I }
      evm (.var "r") = .ok (getTickSourceRAfterMsb3Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsbStep3_r]

theorem evalBinaryOp_getTick_rAfter3Gt2 (I : ExecutionEnv) :
    evalBinaryOp? .gt (getTickSourceRAfterMsb3Value I) (.int 0xF) =
    .ok (.bool (getTickSourceRAfterMsb3Gt2 I)) := by
  unfold getTickSourceRAfterMsb3Value getTickSourceRAfterMsb3Gt2
  simp only [evalBinaryOp?]
  by_cases h : getTickSourceRAfterMsb3Nat I > 0xF
  · have hInt : ((getTickSourceRAfterMsb3Nat I : Nat) : Int) > (0xF : Int) := by
      omega
    rw [decide_eq_true hInt, decide_eq_true h]
  · have hInt : ¬(((getTickSourceRAfterMsb3Nat I : Nat) : Int) > (0xF : Int)) := by
      omega
    rw [decide_eq_false hInt, decide_eq_false h]

theorem evalExpr_getTick_msbF2 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbStep3 I } evm
      (.ite (gtE (.var "r") (.intLit 0xF))
        (.intLit (2 ^ (2 : Nat))) (.intLit 0)) =
      .ok (getTickSourceMsbF2Value I) := by
  unfold gtE getTickSourceMsbF2Value getTickSourceMsbF2Nat
  simp only [evalExpr?, evalExpr_getTick_rVar_afterMsbStep3, EvalResult.bind, bind, pure]
  rw [evalBinaryOp_getTick_rAfter3Gt2]
  cases getTickSourceRAfterMsb3Gt2 I <;> rfl

theorem getTickSourceMsbF2Nat_le_4 (I : ExecutionEnv) :
    getTickSourceMsbF2Nat I ≤ 4 := by
  unfold getTickSourceMsbF2Nat
  split <;> norm_num

theorem getTickStoreAfterF2Let_msb (I : ExecutionEnv) :
    (getTickStoreAfterF2Let I).get? "msb" = some (getTickSourceMsbAfter3Value I) := by
  rw [getTickStoreAfterF2Let]
  rw [store_get_ne (getTickStoreAfterMsbStep3 I) (k := "f") (a := "msb")
    (getTickSourceMsbF2Value I) (by decide)]
  rw [getTickStoreAfterMsbStep3]
  rw [store_get_ne (getTickStoreAfterMsb3 I) (k := "r") (a := "msb")
    (getTickSourceRAfterMsb3Value I) (by decide)]
  exact getTickStoreAfterMsb3_msb I

theorem getTickStoreAfterF2Let_f (I : ExecutionEnv) :
    (getTickStoreAfterF2Let I).get? "f" = some (getTickSourceMsbF2Value I) := by
  rw [getTickStoreAfterF2Let, store_get_self]

theorem evalExpr_getTick_msb_add_f2 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterF2Let I } evm
      (addE (.var "msb") (.var "f")) = .ok (getTickSourceMsbAfter2Value I) := by
  unfold addE getTickSourceMsbAfter2Value getTickSourceMsbAfter2Nat
  simp only [evalExpr?, EvalResult.ofOption, getTickStoreAfterF2Let_msb,
    getTickStoreAfterF2Let_f, getTickSourceMsbAfter3Value, getTickSourceMsbF2Value,
    EvalResult.bind, bind, evalBinaryOp?]
  rw [(Nat.cast_add (getTickSourceMsbAfter3Nat I) (getTickSourceMsbF2Nat I)).symm]

theorem assignStorageRef_getTick_msb_afterF2 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterF2Let I }
      evm .localVar (varRef "msb") (getTickSourceMsbAfter2Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterMsb2 I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterF2Let_msb]
  simp [getTickStoreAfterMsb2, updateLocalPath?, pure, bind, EvalResult.bind]

theorem getTickStoreAfterMsb2_r (I : ExecutionEnv) :
    (getTickStoreAfterMsb2 I).get? "r" = some (getTickSourceRAfterMsb3Value I) := by
  rw [getTickStoreAfterMsb2]
  rw [store_get_ne (getTickStoreAfterF2Let I) (k := "msb") (a := "r")
    (getTickSourceMsbAfter2Value I) (by decide)]
  rw [getTickStoreAfterF2Let]
  rw [store_get_ne (getTickStoreAfterMsbStep3 I) (k := "f") (a := "r")
    (getTickSourceMsbF2Value I) (by decide)]
  exact getTickStoreAfterMsbStep3_r I

theorem getTickStoreAfterMsb2_f (I : ExecutionEnv) :
    (getTickStoreAfterMsb2 I).get? "f" = some (getTickSourceMsbF2Value I) := by
  rw [getTickStoreAfterMsb2]
  rw [store_get_ne (getTickStoreAfterF2Let I) (k := "msb") (a := "f")
    (getTickSourceMsbAfter2Value I) (by decide)]
  exact getTickStoreAfterF2Let_f I

theorem evalExpr_getTick_rVar_afterMsb2 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb2 I }
      evm (.var "r") = .ok (getTickSourceRAfterMsb3Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsb2_r]

theorem evalExpr_getTick_fVar_afterMsb2 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb2 I }
      evm (.var "f") = .ok (getTickSourceMsbF2Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsb2_f]

theorem evalExpr_getTick_r_shr_f2 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb2 I } evm
      (shrE (.var "r") (.var "f")) = .ok (getTickSourceRAfterMsb2Value I) := by
  unfold shrE
  simp only [evalExpr?, evalExpr_getTick_rVar_afterMsb2,
    evalExpr_getTick_fVar_afterMsb2, EvalResult.bind, bind]
  change evalBinaryOp? .shr (.int (Int.ofNat (getTickSourceRAfterMsb3Nat I)))
      (.int (Int.ofNat (getTickSourceMsbF2Nat I))) =
    .ok (getTickSourceRAfterMsb2Value I)
  rw [evalBinaryOp_int_shr_ok]
  · unfold getTickSourceRAfterMsb2Value getTickSourceRAfterMsb2Nat
    rw [intOfNat_toNat_div_pow_cast]
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_lt.mpr (getTickSourceRAfterMsb3Nat_lt_wordModulus I)
  · exact Int.natCast_nonneg _
  · have hle := getTickSourceMsbF2Nat_le_4 I
    have hltNat : getTickSourceMsbF2Nat I < 256 := by omega
    exact Int.ofNat_lt.mpr hltNat

theorem assignStorageRef_getTick_r_afterF2 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterMsb2 I }
      evm .localVar (varRef "r") (getTickSourceRAfterMsb2Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterMsbStep2 I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterMsb2_r]
  simp [getTickStoreAfterMsbStep2, updateLocalPath?, pure, bind, EvalResult.bind]

theorem uniswapV3PoolGetTickAtSqrtRatioSourceMsbStep2 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterMsbStep3 I } evm
      (msbStep 2 0xF)
      (.ok { contract := contract v, locals := getTickStoreAfterMsbStep2 I } evm) := by
  change ExecBlock (config v)
      { contract := contract v, locals := getTickStoreAfterMsbStep3 I } evm
      [ .letDecl "f" (some uint256)
          (.ite (gtE (.var "r") (.intLit 0xF))
            (.intLit (2 ^ (2 : Nat))) (.intLit 0)),
        .assign .localVar (varRef "msb") (addE (.var "msb") (.var "f")),
        .assign .localVar (varRef "r") (shrE (.var "r") (.var "f")) ]
      (.ok { contract := contract v, locals := getTickStoreAfterMsbStep2 I } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_getTick_msbF2 evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_msb_add_f2 evm I)
      (assignStorageRef_getTick_msb_afterF2 evm I)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_r_shr_f2 evm I)
      (assignStorageRef_getTick_r_afterF2 evm I))
    ExecBlock.nil

theorem uniswapV3PoolGetTickAtSqrtRatioSourceMsbSteps765432 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreWithMsb I } evm
      (msbStep 7 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF ++
        msbStep 6 0xFFFFFFFFFFFFFFFF ++
        msbStep 5 0xFFFFFFFF ++
        msbStep 4 0xFFFF ++
        msbStep 3 0xFF ++
        msbStep 2 0xF)
      (.ok { contract := contract v, locals := getTickStoreAfterMsbStep2 I } evm) := by
  exact execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceMsbSteps76543 evm I)
    (uniswapV3PoolGetTickAtSqrtRatioSourceMsbStep2 evm I)

def getTickSourceRAfterMsb2Gt1 (I : ExecutionEnv) : Bool :=
  decide (getTickSourceRAfterMsb2Nat I > 0x3)

def getTickSourceMsbF1Nat (I : ExecutionEnv) : Nat :=
  if getTickSourceRAfterMsb2Gt1 I then 2 ^ (1 : Nat) else 0

def getTickSourceMsbF1Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceMsbF1Nat I)

def getTickStoreAfterF1Let (I : ExecutionEnv) : Store :=
  (getTickStoreAfterMsbStep2 I).insert "f" (getTickSourceMsbF1Value I)

def getTickSourceMsbAfter1Nat (I : ExecutionEnv) : Nat :=
  getTickSourceMsbAfter2Nat I + getTickSourceMsbF1Nat I

def getTickSourceMsbAfter1Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceMsbAfter1Nat I)

def getTickStoreAfterMsb1 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterF1Let I).insert "msb" (getTickSourceMsbAfter1Value I)

def getTickSourceRAfterMsb1Nat (I : ExecutionEnv) : Nat :=
  getTickSourceRAfterMsb2Nat I / 2 ^ getTickSourceMsbF1Nat I

def getTickSourceRAfterMsb1Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceRAfterMsb1Nat I)

def getTickStoreAfterMsbStep1 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterMsb1 I).insert "r" (getTickSourceRAfterMsb1Value I)

theorem getTickSourceRAfterMsb2Nat_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceRAfterMsb2Nat I < EVM.wordModulus := by
  unfold getTickSourceRAfterMsb2Nat
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (getTickSourceRAfterMsb3Nat_lt_wordModulus I)

theorem getTickStoreAfterMsb2_msb (I : ExecutionEnv) :
    (getTickStoreAfterMsb2 I).get? "msb" = some (getTickSourceMsbAfter2Value I) := by
  rw [getTickStoreAfterMsb2, store_get_self]

theorem getTickStoreAfterMsbStep2_r (I : ExecutionEnv) :
    (getTickStoreAfterMsbStep2 I).get? "r" =
      some (getTickSourceRAfterMsb2Value I) := by
  rw [getTickStoreAfterMsbStep2, store_get_self]

theorem getTickStoreAfterMsbStep2_msb (I : ExecutionEnv) :
    (getTickStoreAfterMsbStep2 I).get? "msb" =
      some (getTickSourceMsbAfter2Value I) := by
  rw [getTickStoreAfterMsbStep2]
  rw [store_get_ne (getTickStoreAfterMsb2 I) (k := "r") (a := "msb")
    (getTickSourceRAfterMsb2Value I) (by decide)]
  exact getTickStoreAfterMsb2_msb I

theorem evalExpr_getTick_rVar_afterMsbStep2 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbStep2 I }
      evm (.var "r") = .ok (getTickSourceRAfterMsb2Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsbStep2_r]

theorem evalBinaryOp_getTick_rAfter2Gt1 (I : ExecutionEnv) :
    evalBinaryOp? .gt (getTickSourceRAfterMsb2Value I) (.int 0x3) =
    .ok (.bool (getTickSourceRAfterMsb2Gt1 I)) := by
  unfold getTickSourceRAfterMsb2Value getTickSourceRAfterMsb2Gt1
  simp only [evalBinaryOp?]
  by_cases h : getTickSourceRAfterMsb2Nat I > 0x3
  · have hInt : ((getTickSourceRAfterMsb2Nat I : Nat) : Int) > (0x3 : Int) := by
      omega
    rw [decide_eq_true hInt, decide_eq_true h]
  · have hInt : ¬(((getTickSourceRAfterMsb2Nat I : Nat) : Int) > (0x3 : Int)) := by
      omega
    rw [decide_eq_false hInt, decide_eq_false h]

theorem evalExpr_getTick_msbF1 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbStep2 I } evm
      (.ite (gtE (.var "r") (.intLit 0x3))
        (.intLit (2 ^ (1 : Nat))) (.intLit 0)) =
      .ok (getTickSourceMsbF1Value I) := by
  unfold gtE getTickSourceMsbF1Value getTickSourceMsbF1Nat
  simp only [evalExpr?, evalExpr_getTick_rVar_afterMsbStep2, EvalResult.bind, bind, pure]
  rw [evalBinaryOp_getTick_rAfter2Gt1]
  cases getTickSourceRAfterMsb2Gt1 I <;> rfl

theorem getTickSourceMsbF1Nat_le_2 (I : ExecutionEnv) :
    getTickSourceMsbF1Nat I ≤ 2 := by
  unfold getTickSourceMsbF1Nat
  split <;> norm_num

theorem getTickStoreAfterF1Let_msb (I : ExecutionEnv) :
    (getTickStoreAfterF1Let I).get? "msb" = some (getTickSourceMsbAfter2Value I) := by
  rw [getTickStoreAfterF1Let]
  rw [store_get_ne (getTickStoreAfterMsbStep2 I) (k := "f") (a := "msb")
    (getTickSourceMsbF1Value I) (by decide)]
  rw [getTickStoreAfterMsbStep2]
  rw [store_get_ne (getTickStoreAfterMsb2 I) (k := "r") (a := "msb")
    (getTickSourceRAfterMsb2Value I) (by decide)]
  exact getTickStoreAfterMsb2_msb I

theorem getTickStoreAfterF1Let_f (I : ExecutionEnv) :
    (getTickStoreAfterF1Let I).get? "f" = some (getTickSourceMsbF1Value I) := by
  rw [getTickStoreAfterF1Let, store_get_self]

theorem evalExpr_getTick_msb_add_f1 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterF1Let I } evm
      (addE (.var "msb") (.var "f")) = .ok (getTickSourceMsbAfter1Value I) := by
  unfold addE getTickSourceMsbAfter1Value getTickSourceMsbAfter1Nat
  simp only [evalExpr?, EvalResult.ofOption, getTickStoreAfterF1Let_msb,
    getTickStoreAfterF1Let_f, getTickSourceMsbAfter2Value, getTickSourceMsbF1Value,
    EvalResult.bind, bind, evalBinaryOp?]
  rw [(Nat.cast_add (getTickSourceMsbAfter2Nat I) (getTickSourceMsbF1Nat I)).symm]

theorem assignStorageRef_getTick_msb_afterF1 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterF1Let I }
      evm .localVar (varRef "msb") (getTickSourceMsbAfter1Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterMsb1 I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterF1Let_msb]
  simp [getTickStoreAfterMsb1, updateLocalPath?, pure, bind, EvalResult.bind]

theorem getTickStoreAfterMsb1_r (I : ExecutionEnv) :
    (getTickStoreAfterMsb1 I).get? "r" = some (getTickSourceRAfterMsb2Value I) := by
  rw [getTickStoreAfterMsb1]
  rw [store_get_ne (getTickStoreAfterF1Let I) (k := "msb") (a := "r")
    (getTickSourceMsbAfter1Value I) (by decide)]
  rw [getTickStoreAfterF1Let]
  rw [store_get_ne (getTickStoreAfterMsbStep2 I) (k := "f") (a := "r")
    (getTickSourceMsbF1Value I) (by decide)]
  exact getTickStoreAfterMsbStep2_r I

theorem getTickStoreAfterMsb1_f (I : ExecutionEnv) :
    (getTickStoreAfterMsb1 I).get? "f" = some (getTickSourceMsbF1Value I) := by
  rw [getTickStoreAfterMsb1]
  rw [store_get_ne (getTickStoreAfterF1Let I) (k := "msb") (a := "f")
    (getTickSourceMsbAfter1Value I) (by decide)]
  exact getTickStoreAfterF1Let_f I

theorem evalExpr_getTick_rVar_afterMsb1 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb1 I }
      evm (.var "r") = .ok (getTickSourceRAfterMsb2Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsb1_r]

theorem evalExpr_getTick_fVar_afterMsb1 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb1 I }
      evm (.var "f") = .ok (getTickSourceMsbF1Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsb1_f]

theorem evalExpr_getTick_r_shr_f1 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb1 I } evm
      (shrE (.var "r") (.var "f")) = .ok (getTickSourceRAfterMsb1Value I) := by
  unfold shrE
  simp only [evalExpr?, evalExpr_getTick_rVar_afterMsb1,
    evalExpr_getTick_fVar_afterMsb1, EvalResult.bind, bind]
  change evalBinaryOp? .shr (.int (Int.ofNat (getTickSourceRAfterMsb2Nat I)))
      (.int (Int.ofNat (getTickSourceMsbF1Nat I))) =
    .ok (getTickSourceRAfterMsb1Value I)
  rw [evalBinaryOp_int_shr_ok]
  · unfold getTickSourceRAfterMsb1Value getTickSourceRAfterMsb1Nat
    rw [intOfNat_toNat_div_pow_cast]
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_lt.mpr (getTickSourceRAfterMsb2Nat_lt_wordModulus I)
  · exact Int.natCast_nonneg _
  · have hle := getTickSourceMsbF1Nat_le_2 I
    have hltNat : getTickSourceMsbF1Nat I < 256 := by omega
    exact Int.ofNat_lt.mpr hltNat

theorem assignStorageRef_getTick_r_afterF1 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterMsb1 I }
      evm .localVar (varRef "r") (getTickSourceRAfterMsb1Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterMsbStep1 I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterMsb1_r]
  simp [getTickStoreAfterMsbStep1, updateLocalPath?, pure, bind, EvalResult.bind]

theorem uniswapV3PoolGetTickAtSqrtRatioSourceMsbStep1 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterMsbStep2 I } evm
      (msbStep 1 0x3)
      (.ok { contract := contract v, locals := getTickStoreAfterMsbStep1 I } evm) := by
  change ExecBlock (config v)
      { contract := contract v, locals := getTickStoreAfterMsbStep2 I } evm
      [ .letDecl "f" (some uint256)
          (.ite (gtE (.var "r") (.intLit 0x3))
            (.intLit (2 ^ (1 : Nat))) (.intLit 0)),
        .assign .localVar (varRef "msb") (addE (.var "msb") (.var "f")),
        .assign .localVar (varRef "r") (shrE (.var "r") (.var "f")) ]
      (.ok { contract := contract v, locals := getTickStoreAfterMsbStep1 I } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_getTick_msbF1 evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_msb_add_f1 evm I)
      (assignStorageRef_getTick_msb_afterF1 evm I)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_r_shr_f1 evm I)
      (assignStorageRef_getTick_r_afterF1 evm I))
    ExecBlock.nil

theorem uniswapV3PoolGetTickAtSqrtRatioSourceMsbSteps7654321 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreWithMsb I } evm
      (msbStep 7 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF ++
        msbStep 6 0xFFFFFFFFFFFFFFFF ++
        msbStep 5 0xFFFFFFFF ++
        msbStep 4 0xFFFF ++
        msbStep 3 0xFF ++
        msbStep 2 0xF ++
        msbStep 1 0x3)
      (.ok { contract := contract v, locals := getTickStoreAfterMsbStep1 I } evm) := by
  exact execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceMsbSteps765432 evm I)
    (uniswapV3PoolGetTickAtSqrtRatioSourceMsbStep1 evm I)

def getTickSourceRAfterMsb1Gt0 (I : ExecutionEnv) : Bool :=
  decide (getTickSourceRAfterMsb1Nat I > 0x1)

def getTickSourceMsbF0Nat (I : ExecutionEnv) : Nat :=
  if getTickSourceRAfterMsb1Gt0 I then 1 else 0

def getTickSourceMsbF0Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceMsbF0Nat I)

def getTickStoreAfterF0Let (I : ExecutionEnv) : Store :=
  (getTickStoreAfterMsbStep1 I).insert "f" (getTickSourceMsbF0Value I)

def getTickSourceMsbAfter0Nat (I : ExecutionEnv) : Nat :=
  getTickSourceMsbAfter1Nat I + getTickSourceMsbF0Nat I

def getTickSourceMsbAfter0Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceMsbAfter0Nat I)

def getTickStoreAfterMsbCombine (I : ExecutionEnv) : Store :=
  (getTickStoreAfterF0Let I).insert "msb" (getTickSourceMsbAfter0Value I)

theorem getTickStoreAfterMsb1_msb (I : ExecutionEnv) :
    (getTickStoreAfterMsb1 I).get? "msb" = some (getTickSourceMsbAfter1Value I) := by
  rw [getTickStoreAfterMsb1, store_get_self]

theorem getTickStoreAfterMsbStep1_r (I : ExecutionEnv) :
    (getTickStoreAfterMsbStep1 I).get? "r" =
      some (getTickSourceRAfterMsb1Value I) := by
  rw [getTickStoreAfterMsbStep1, store_get_self]

theorem getTickStoreAfterMsbStep1_msb (I : ExecutionEnv) :
    (getTickStoreAfterMsbStep1 I).get? "msb" =
      some (getTickSourceMsbAfter1Value I) := by
  rw [getTickStoreAfterMsbStep1]
  rw [store_get_ne (getTickStoreAfterMsb1 I) (k := "r") (a := "msb")
    (getTickSourceRAfterMsb1Value I) (by decide)]
  exact getTickStoreAfterMsb1_msb I

theorem evalExpr_getTick_rVar_afterMsbStep1 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbStep1 I }
      evm (.var "r") = .ok (getTickSourceRAfterMsb1Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsbStep1_r]

theorem evalBinaryOp_getTick_rAfter1Gt0 (I : ExecutionEnv) :
    evalBinaryOp? .gt (getTickSourceRAfterMsb1Value I) (.int 0x1) =
    .ok (.bool (getTickSourceRAfterMsb1Gt0 I)) := by
  unfold getTickSourceRAfterMsb1Value getTickSourceRAfterMsb1Gt0
  simp only [evalBinaryOp?]
  by_cases h : getTickSourceRAfterMsb1Nat I > 0x1
  · have hInt : ((getTickSourceRAfterMsb1Nat I : Nat) : Int) > (0x1 : Int) := by
      omega
    rw [decide_eq_true hInt, decide_eq_true h]
  · have hInt : ¬(((getTickSourceRAfterMsb1Nat I : Nat) : Int) > (0x1 : Int)) := by
      omega
    rw [decide_eq_false hInt, decide_eq_false h]

theorem evalExpr_getTick_msbF0 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbStep1 I } evm
      (.ite (gtE (.var "r") (.intLit 0x1)) (.intLit 1) (.intLit 0)) =
      .ok (getTickSourceMsbF0Value I) := by
  unfold gtE getTickSourceMsbF0Value getTickSourceMsbF0Nat
  simp only [evalExpr?, evalExpr_getTick_rVar_afterMsbStep1, EvalResult.bind, bind, pure]
  rw [evalBinaryOp_getTick_rAfter1Gt0]
  cases getTickSourceRAfterMsb1Gt0 I <;> rfl

theorem getTickStoreAfterF0Let_msb (I : ExecutionEnv) :
    (getTickStoreAfterF0Let I).get? "msb" = some (getTickSourceMsbAfter1Value I) := by
  rw [getTickStoreAfterF0Let]
  rw [store_get_ne (getTickStoreAfterMsbStep1 I) (k := "f") (a := "msb")
    (getTickSourceMsbF0Value I) (by decide)]
  exact getTickStoreAfterMsbStep1_msb I

theorem getTickStoreAfterF0Let_f (I : ExecutionEnv) :
    (getTickStoreAfterF0Let I).get? "f" = some (getTickSourceMsbF0Value I) := by
  rw [getTickStoreAfterF0Let, store_get_self]

theorem evalExpr_getTick_msb_add_f0 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterF0Let I } evm
      (addE (.var "msb") (.var "f")) = .ok (getTickSourceMsbAfter0Value I) := by
  unfold addE getTickSourceMsbAfter0Value getTickSourceMsbAfter0Nat
  simp only [evalExpr?, EvalResult.ofOption, getTickStoreAfterF0Let_msb,
    getTickStoreAfterF0Let_f, getTickSourceMsbAfter1Value, getTickSourceMsbF0Value,
    EvalResult.bind, bind, evalBinaryOp?]
  rw [(Nat.cast_add (getTickSourceMsbAfter1Nat I) (getTickSourceMsbF0Nat I)).symm]

theorem assignStorageRef_getTick_msb_afterF0 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterF0Let I }
      evm .localVar (varRef "msb") (getTickSourceMsbAfter0Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterMsbCombine I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterF0Let_msb]
  simp [getTickStoreAfterMsbCombine, updateLocalPath?, pure, bind, EvalResult.bind]

theorem uniswapV3PoolGetTickAtSqrtRatioSourceMsbCombine {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterMsbStep1 I } evm
      [ .letDecl "f" (some uint256)
          (.ite (gtE (.var "r") (.intLit 0x1)) (.intLit 1) (.intLit 0)),
        .assign .localVar (varRef "msb") (addE (.var "msb") (.var "f")) ]
      (.ok { contract := contract v, locals := getTickStoreAfterMsbCombine I } evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_getTick_msbF0 evm I)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_msb_add_f0 evm I)
      (assignStorageRef_getTick_msb_afterF0 evm I))
    ExecBlock.nil

theorem uniswapV3PoolGetTickAtSqrtRatioSourceMsbSteps76543210 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreWithMsb I } evm
      (msbStep 7 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF ++
        msbStep 6 0xFFFFFFFFFFFFFFFF ++
        msbStep 5 0xFFFFFFFF ++
        msbStep 4 0xFFFF ++
        msbStep 3 0xFF ++
        msbStep 2 0xF ++
        msbStep 1 0x3 ++
        [ .letDecl "f" (some uint256)
            (.ite (gtE (.var "r") (.intLit 0x1)) (.intLit 1) (.intLit 0)),
          .assign .localVar (varRef "msb") (addE (.var "msb") (.var "f")) ])
      (.ok { contract := contract v, locals := getTickStoreAfterMsbCombine I } evm) := by
  exact execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceMsbSteps7654321 evm I)
    (uniswapV3PoolGetTickAtSqrtRatioSourceMsbCombine evm I)

def getTickSourceMsbGe128 (I : ExecutionEnv) : Bool :=
  decide (128 ≤ getTickSourceMsbAfter0Nat I)

def getTickSourceRNormalizedHighNat (I : ExecutionEnv) : Nat :=
  getTickSourceRatioNat I / 2 ^ (getTickSourceMsbAfter0Nat I - 127)

def getTickSourceRNormalizedLowNat (I : ExecutionEnv) : Nat :=
  (getTickSourceRatioNat I * 2 ^ (127 - getTickSourceMsbAfter0Nat I)) % EVM.wordModulus

def getTickSourceRNormalizedNat (I : ExecutionEnv) : Nat :=
  if getTickSourceMsbGe128 I then
    getTickSourceRNormalizedHighNat I
  else
    getTickSourceRNormalizedLowNat I

def getTickSourceRNormalizedValue (I : ExecutionEnv) : Value :=
  .int (getTickSourceRNormalizedNat I)

def getTickStoreAfterNormalizeR (I : ExecutionEnv) : Store :=
  (getTickStoreAfterMsbCombine I).insert "r" (getTickSourceRNormalizedValue I)

theorem getTickSourceMsbF0Nat_le_1 (I : ExecutionEnv) :
    getTickSourceMsbF0Nat I ≤ 1 := by
  unfold getTickSourceMsbF0Nat
  split <;> norm_num

theorem getTickSourceMsbAfter0Nat_le_255 (I : ExecutionEnv) :
    getTickSourceMsbAfter0Nat I ≤ 255 := by
  have h7 := getTickSourceMsbF7Nat_le_128 I
  have h6 := getTickSourceMsbF6Nat_le_64 I
  have h5 := getTickSourceMsbF5Nat_le_32 I
  have h4 := getTickSourceMsbF4Nat_le_16 I
  have h3 := getTickSourceMsbF3Nat_le_8 I
  have h2 := getTickSourceMsbF2Nat_le_4 I
  have h1 := getTickSourceMsbF1Nat_le_2 I
  have h0 := getTickSourceMsbF0Nat_le_1 I
  unfold getTickSourceMsbAfter0Nat getTickSourceMsbAfter1Nat getTickSourceMsbAfter2Nat
    getTickSourceMsbAfter3Nat getTickSourceMsbAfter4Nat getTickSourceMsbAfter5Nat
    getTickSourceMsbAfter6Nat
  omega

theorem getTickSourceRNormalizedNat_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceRNormalizedNat I < EVM.wordModulus := by
  unfold getTickSourceRNormalizedNat getTickSourceRNormalizedHighNat
    getTickSourceRNormalizedLowNat
  by_cases h : getTickSourceMsbGe128 I
  · rw [if_pos h]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (getTickSourceRatioNat_lt_wordModulus I)
  · rw [if_neg h]
    exact Nat.mod_lt _ (by native_decide : 0 < EVM.wordModulus)

theorem evalBinaryOp_int_shl_ok {x s : Int}
    (hx0 : 0 ≤ x) (hxlt : x < (EVM.wordModulus : Int))
    (hs0 : 0 ≤ s) (hslt : s < 256) :
    evalBinaryOp? .shl (.int x) (.int s) =
      .ok (.int ((x.toNat * 2 ^ s.toNat) % EVM.wordModulus)) := by
  simp only [evalBinaryOp?]
  rw [if_pos ⟨hx0, hxlt, hs0⟩]
  rw [if_neg]
  omega

theorem intOfNat_toNat_mul_pow_mod_cast (n s : Nat) :
    (((Int.ofNat n).toNat * 2 ^ (Int.ofNat s).toNat % EVM.wordModulus : Nat) : Int) =
      (n * 2 ^ s % EVM.wordModulus : Nat) := by
  rfl

theorem getTickStoreAfterMsbCombine_msb (I : ExecutionEnv) :
    (getTickStoreAfterMsbCombine I).get? "msb" =
      some (getTickSourceMsbAfter0Value I) := by
  rw [getTickStoreAfterMsbCombine, store_get_self]

theorem getTickStoreAfterMsbCombine_r (I : ExecutionEnv) :
    (getTickStoreAfterMsbCombine I).get? "r" =
      some (getTickSourceRAfterMsb1Value I) := by
  rw [getTickStoreAfterMsbCombine]
  rw [store_get_ne (getTickStoreAfterF0Let I) (k := "msb") (a := "r")
    (getTickSourceMsbAfter0Value I) (by decide)]
  rw [getTickStoreAfterF0Let]
  rw [store_get_ne (getTickStoreAfterMsbStep1 I) (k := "f") (a := "r")
    (getTickSourceMsbF0Value I) (by decide)]
  exact getTickStoreAfterMsbStep1_r I

theorem getTickStoreAfterMsbCombine_ratio (I : ExecutionEnv) :
    (getTickStoreAfterMsbCombine I).get? "ratio" = some (getTickSourceRatioValue I) := by
  rw [getTickStoreAfterMsbCombine]
  rw [store_get_ne (getTickStoreAfterF0Let I) (k := "msb") (a := "ratio")
    (getTickSourceMsbAfter0Value I) (by decide)]
  rw [getTickStoreAfterF0Let]
  rw [store_get_ne (getTickStoreAfterMsbStep1 I) (k := "f") (a := "ratio")
    (getTickSourceMsbF0Value I) (by decide)]
  rw [getTickStoreAfterMsbStep1]
  rw [store_get_ne (getTickStoreAfterMsb1 I) (k := "r") (a := "ratio")
    (getTickSourceRAfterMsb1Value I) (by decide)]
  rw [getTickStoreAfterMsb1]
  rw [store_get_ne (getTickStoreAfterF1Let I) (k := "msb") (a := "ratio")
    (getTickSourceMsbAfter1Value I) (by decide)]
  rw [getTickStoreAfterF1Let]
  rw [store_get_ne (getTickStoreAfterMsbStep2 I) (k := "f") (a := "ratio")
    (getTickSourceMsbF1Value I) (by decide)]
  rw [getTickStoreAfterMsbStep2]
  rw [store_get_ne (getTickStoreAfterMsb2 I) (k := "r") (a := "ratio")
    (getTickSourceRAfterMsb2Value I) (by decide)]
  rw [getTickStoreAfterMsb2]
  rw [store_get_ne (getTickStoreAfterF2Let I) (k := "msb") (a := "ratio")
    (getTickSourceMsbAfter2Value I) (by decide)]
  rw [getTickStoreAfterF2Let]
  rw [store_get_ne (getTickStoreAfterMsbStep3 I) (k := "f") (a := "ratio")
    (getTickSourceMsbF2Value I) (by decide)]
  rw [getTickStoreAfterMsbStep3]
  rw [store_get_ne (getTickStoreAfterMsb3 I) (k := "r") (a := "ratio")
    (getTickSourceRAfterMsb3Value I) (by decide)]
  rw [getTickStoreAfterMsb3]
  rw [store_get_ne (getTickStoreAfterF3Let I) (k := "msb") (a := "ratio")
    (getTickSourceMsbAfter3Value I) (by decide)]
  rw [getTickStoreAfterF3Let]
  rw [store_get_ne (getTickStoreAfterMsbStep4 I) (k := "f") (a := "ratio")
    (getTickSourceMsbF3Value I) (by decide)]
  rw [getTickStoreAfterMsbStep4]
  rw [store_get_ne (getTickStoreAfterMsb4 I) (k := "r") (a := "ratio")
    (getTickSourceRAfterMsb4Value I) (by decide)]
  rw [getTickStoreAfterMsb4]
  rw [store_get_ne (getTickStoreAfterF4Let I) (k := "msb") (a := "ratio")
    (getTickSourceMsbAfter4Value I) (by decide)]
  rw [getTickStoreAfterF4Let]
  rw [store_get_ne (getTickStoreAfterMsbStep5 I) (k := "f") (a := "ratio")
    (getTickSourceMsbF4Value I) (by decide)]
  rw [getTickStoreAfterMsbStep5]
  rw [store_get_ne (getTickStoreAfterMsb5 I) (k := "r") (a := "ratio")
    (getTickSourceRAfterMsb5Value I) (by decide)]
  rw [getTickStoreAfterMsb5]
  rw [store_get_ne (getTickStoreAfterF5Let I) (k := "msb") (a := "ratio")
    (getTickSourceMsbAfter5Value I) (by decide)]
  rw [getTickStoreAfterF5Let]
  rw [store_get_ne (getTickStoreAfterMsbStep6 I) (k := "f") (a := "ratio")
    (getTickSourceMsbF5Value I) (by decide)]
  rw [getTickStoreAfterMsbStep6]
  rw [store_get_ne (getTickStoreAfterMsb6 I) (k := "r") (a := "ratio")
    (getTickSourceRAfterMsb6Value I) (by decide)]
  rw [getTickStoreAfterMsb6]
  rw [store_get_ne (getTickStoreAfterF6Let I) (k := "msb") (a := "ratio")
    (getTickSourceMsbAfter6Value I) (by decide)]
  rw [getTickStoreAfterF6Let]
  rw [store_get_ne (getTickStoreAfterMsbStep7 I) (k := "f") (a := "ratio")
    (getTickSourceMsbF6Value I) (by decide)]
  rw [getTickStoreAfterMsbStep7]
  rw [store_get_ne (getTickStoreAfterMsb7 I) (k := "r") (a := "ratio")
    (getTickSourceRAfterMsb7Value I) (by decide)]
  rw [getTickStoreAfterMsb7]
  rw [store_get_ne (getTickStoreAfterF7Let I) (k := "msb") (a := "ratio")
    (getTickSourceMsbAfter7Value I) (by decide)]
  rw [getTickStoreAfterF7Let]
  rw [store_get_ne (getTickStoreWithMsb I) (k := "f") (a := "ratio")
    (getTickSourceMsbF7Value I) (by decide)]
  rw [getTickStoreWithMsb]
  rw [store_get_ne (getTickStoreWithR I) (k := "msb") (a := "ratio")
    getTickSourceMsbValue (by decide)]
  rw [getTickStoreWithR]
  rw [store_get_ne (getTickStoreWithRatio I) (k := "r") (a := "ratio")
    (getTickSourceRatioValue I) (by decide)]
  exact getTickStoreWithRatio_ratio I

theorem evalExpr_getTick_msbVar_afterMsbCombine {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbCombine I }
      evm (.var "msb") = .ok (getTickSourceMsbAfter0Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsbCombine_msb]

theorem evalExpr_getTick_rVar_afterMsbCombine {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbCombine I }
      evm (.var "r") = .ok (getTickSourceRAfterMsb1Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsbCombine_r]

theorem evalExpr_getTick_ratioVar_afterMsbCombine {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbCombine I }
      evm (.var "ratio") = .ok (getTickSourceRatioValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsbCombine_ratio]

theorem evalBinaryOp_getTick_msbGe128 (I : ExecutionEnv) :
    evalBinaryOp? .ge (getTickSourceMsbAfter0Value I) (.int 128) =
    .ok (.bool (getTickSourceMsbGe128 I)) := by
  unfold getTickSourceMsbAfter0Value getTickSourceMsbGe128
  simp only [evalBinaryOp?]
  by_cases h : 128 ≤ getTickSourceMsbAfter0Nat I
  · have hInt : ((getTickSourceMsbAfter0Nat I : Nat) : Int) ≥ (128 : Int) := by
      omega
    rw [decide_eq_true hInt, decide_eq_true h]
  · have hInt : ¬(((getTickSourceMsbAfter0Nat I : Nat) : Int) ≥ (128 : Int)) := by
      omega
    rw [decide_eq_false hInt, decide_eq_false h]

theorem evalExpr_getTick_msbGe128 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbCombine I }
      evm (geE (.var "msb") (.intLit 128)) =
      .ok (.bool (getTickSourceMsbGe128 I)) := by
  unfold geE
  simp only [evalExpr?, evalExpr_getTick_msbVar_afterMsbCombine, EvalResult.bind, bind,
    pure]
  exact evalBinaryOp_getTick_msbGe128 I

theorem evalExpr_getTick_msbMinus127_high {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) (hge : getTickSourceMsbGe128 I = true) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbCombine I }
      evm (subE (.var "msb") (.intLit 127)) =
      .ok (.int (Int.ofNat (getTickSourceMsbAfter0Nat I - 127))) := by
  have hNat : 128 ≤ getTickSourceMsbAfter0Nat I := by
    unfold getTickSourceMsbGe128 at hge
    exact of_decide_eq_true hge
  unfold subE
  simp only [evalExpr?, evalExpr_getTick_msbVar_afterMsbCombine, EvalResult.bind, bind,
    pure, getTickSourceMsbAfter0Value, evalBinaryOp?]
  congr 2
  exact (Int.ofNat_sub (m := 127) (n := getTickSourceMsbAfter0Nat I) (by omega)).symm

theorem evalExpr_getTick_127MinusMsb_low {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) (hge : getTickSourceMsbGe128 I = false) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbCombine I }
      evm (subE (.intLit 127) (.var "msb")) =
      .ok (.int (Int.ofNat (127 - getTickSourceMsbAfter0Nat I))) := by
  have hNat : getTickSourceMsbAfter0Nat I < 128 := by
    unfold getTickSourceMsbGe128 at hge
    exact Nat.lt_of_not_ge (of_decide_eq_false hge)
  unfold subE
  simp only [evalExpr?, evalExpr_getTick_msbVar_afterMsbCombine, EvalResult.bind, bind,
    pure, getTickSourceMsbAfter0Value, evalBinaryOp?]
  congr 2
  exact (Int.ofNat_sub (m := getTickSourceMsbAfter0Nat I) (n := 127) (by omega)).symm

theorem evalExpr_getTick_normalizeR_high {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) (hge : getTickSourceMsbGe128 I = true) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbCombine I }
      evm (shrE (.var "ratio") (subE (.var "msb") (.intLit 127))) =
      .ok (getTickSourceRNormalizedValue I) := by
  have hNat : 128 ≤ getTickSourceMsbAfter0Nat I := by
    unfold getTickSourceMsbGe128 at hge
    exact of_decide_eq_true hge
  have hShiftLt : getTickSourceMsbAfter0Nat I - 127 < 256 := by
    have hle := getTickSourceMsbAfter0Nat_le_255 I
    omega
  unfold shrE
  simp only [evalExpr?, evalExpr_getTick_ratioVar_afterMsbCombine,
    evalExpr_getTick_msbMinus127_high evm I hge, EvalResult.bind, bind]
  unfold getTickSourceRatioValue
  rw [evalBinaryOp_int_shr_ok]
  · unfold getTickSourceRNormalizedValue getTickSourceRNormalizedNat
      getTickSourceRNormalizedHighNat
    rw [if_pos hge]
    exact congrArg (fun z : Int => (EvalResult.ok (Value.int z) : EvalResult Value))
      (intOfNat_toNat_div_pow_cast (getTickSourceRatioNat I)
        (getTickSourceMsbAfter0Nat I - 127))
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_lt.mpr (getTickSourceRatioNat_lt_wordModulus I)
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_lt.mpr hShiftLt

theorem evalExpr_getTick_normalizeR_low {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) (hge : getTickSourceMsbGe128 I = false) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbCombine I }
      evm (shlE (.var "ratio") (subE (.intLit 127) (.var "msb"))) =
      .ok (getTickSourceRNormalizedValue I) := by
  have hNat : getTickSourceMsbAfter0Nat I < 128 := by
    unfold getTickSourceMsbGe128 at hge
    exact Nat.lt_of_not_ge (of_decide_eq_false hge)
  have hShiftLt : 127 - getTickSourceMsbAfter0Nat I < 256 := by omega
  unfold shlE
  simp only [evalExpr?, evalExpr_getTick_ratioVar_afterMsbCombine,
    evalExpr_getTick_127MinusMsb_low evm I hge, EvalResult.bind, bind]
  unfold getTickSourceRatioValue
  rw [evalBinaryOp_int_shl_ok]
  · unfold getTickSourceRNormalizedValue getTickSourceRNormalizedNat
      getTickSourceRNormalizedLowNat
    rw [if_neg (Bool.eq_false_iff.mp hge)]
    exact congrArg (fun z : Int => (EvalResult.ok (Value.int z) : EvalResult Value))
      (intOfNat_toNat_mul_pow_mod_cast (getTickSourceRatioNat I)
        (127 - getTickSourceMsbAfter0Nat I))
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_lt.mpr (getTickSourceRatioNat_lt_wordModulus I)
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_lt.mpr hShiftLt

theorem assignStorageRef_getTick_r_normalized {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterMsbCombine I }
      evm .localVar (varRef "r") (getTickSourceRNormalizedValue I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterNormalizeR I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterMsbCombine_r]
  simp [getTickStoreAfterNormalizeR, updateLocalPath?, pure, bind, EvalResult.bind]

theorem uniswapV3PoolGetTickAtSqrtRatioSourceNormalizeR {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecStmt (config v) { contract := contract v, locals := getTickStoreAfterMsbCombine I } evm
      (Stmt.ite (geE (.var "msb") (.intLit 128))
        [ .assign .localVar (varRef "r")
            (shrE (.var "ratio") (subE (.var "msb") (.intLit 127))) ]
        [ .assign .localVar (varRef "r")
            (shlE (.var "ratio") (subE (.intLit 127) (.var "msb"))) ])
      (.ok { contract := contract v, locals := getTickStoreAfterNormalizeR I } evm) := by
  by_cases hge : getTickSourceMsbGe128 I = true
  · refine ExecStmt.iteTrue ?_ ?_
    · rw [evalExpr_getTick_msbGe128]
      rw [hge]
    · exact ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_getTick_normalizeR_high evm I hge)
          (assignStorageRef_getTick_r_normalized evm I))
        ExecBlock.nil
  · have hfalse : getTickSourceMsbGe128 I = false := by
      exact Bool.eq_false_iff.mpr hge
    refine ExecStmt.iteFalse ?_ ?_
    · rw [evalExpr_getTick_msbGe128]
      rw [hfalse]
    · exact ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_getTick_normalizeR_low evm I hfalse)
          (assignStorageRef_getTick_r_normalized evm I))
        ExecBlock.nil

theorem uniswapV3PoolGetTickAtSqrtRatioSourceThroughNormalizeR {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreWithMsb I } evm
      (msbStep 7 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF ++
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
                (shlE (.var "ratio") (subE (.intLit 127) (.var "msb"))) ] ])
      (.ok { contract := contract v, locals := getTickStoreAfterNormalizeR I } evm) := by
  change ExecBlock (config v) { contract := contract v, locals := getTickStoreWithMsb I } evm
      ((msbStep 7 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF ++
        msbStep 6 0xFFFFFFFFFFFFFFFF ++
        msbStep 5 0xFFFFFFFF ++
        msbStep 4 0xFFFF ++
        msbStep 3 0xFF ++
        msbStep 2 0xF ++
        msbStep 1 0x3 ++
        [ .letDecl "f" (some uint256)
            (.ite (gtE (.var "r") (.intLit 0x1)) (.intLit 1) (.intLit 0)),
          .assign .localVar (varRef "msb") (addE (.var "msb") (.var "f")) ]) ++
        [ Stmt.ite (geE (.var "msb") (.intLit 128))
            [ .assign .localVar (varRef "r")
                (shrE (.var "ratio") (subE (.var "msb") (.intLit 127))) ]
            [ .assign .localVar (varRef "r")
                (shlE (.var "ratio") (subE (.intLit 127) (.var "msb"))) ] ])
      (.ok { contract := contract v, locals := getTickStoreAfterNormalizeR I } evm)
  exact execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceMsbSteps76543210 evm I)
    (ExecBlock.consNormal (uniswapV3PoolGetTickAtSqrtRatioSourceNormalizeR evm I)
      ExecBlock.nil)

def getTickSourceLog2BaseInt (I : ExecutionEnv) : Int :=
  ((getTickSourceMsbAfter0Nat I : Int) - 128) * (2 ^ (64 : Nat) : Int)

def getTickSourceLog2BaseValue (I : ExecutionEnv) : Value :=
  .int (getTickSourceLog2BaseInt I)

def getTickStoreAfterLog2BaseLet (I : ExecutionEnv) : Store :=
  (getTickStoreAfterNormalizeR I).insert "log_2" (getTickSourceLog2BaseValue I)

theorem getTickStoreAfterNormalizeR_msb (I : ExecutionEnv) :
    (getTickStoreAfterNormalizeR I).get? "msb" =
      some (getTickSourceMsbAfter0Value I) := by
  rw [getTickStoreAfterNormalizeR]
  rw [store_get_ne (getTickStoreAfterMsbCombine I) (k := "r") (a := "msb")
    (getTickSourceRNormalizedValue I) (by decide)]
  exact getTickStoreAfterMsbCombine_msb I

theorem evalExpr_getTick_msbVar_afterNormalizeR {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterNormalizeR I }
      evm (.var "msb") = .ok (getTickSourceMsbAfter0Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterNormalizeR_msb]

theorem evalExpr_getTick_msbMinus128 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterNormalizeR I }
      evm (subE (.var "msb") (.intLit 128)) =
      .ok (.int ((getTickSourceMsbAfter0Nat I : Int) - 128)) := by
  unfold subE
  simp only [evalExpr?, evalExpr_getTick_msbVar_afterNormalizeR, getTickSourceMsbAfter0Value,
    EvalResult.bind, bind, pure, evalBinaryOp?]

theorem evalExpr_getTick_log2Base {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterNormalizeR I }
      evm (mulE (subE (.var "msb") (.intLit 128)) (.intLit (2 ^ (64 : Nat)))) =
      .ok (getTickSourceLog2BaseValue I) := by
  unfold mulE getTickSourceLog2BaseValue getTickSourceLog2BaseInt
  simp only [evalExpr?, evalExpr_getTick_msbMinus128, EvalResult.bind, bind, pure,
    evalBinaryOp?]

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLog2BaseLet {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterNormalizeR I }
      evm
      [ .letDecl "log_2" (some int256)
          (mulE (subE (.var "msb") (.intLit 128)) (.intLit (2 ^ (64 : Nat)))) ]
      (.ok { contract := contract v, locals := getTickStoreAfterLog2BaseLet I } evm) := by
  exact ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_getTick_log2Base evm I))
    ExecBlock.nil

theorem uniswapV3PoolGetTickAtSqrtRatioSourceThroughLog2Base {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreWithMsb I } evm
      (msbStep 7 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF ++
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
            (mulE (subE (.var "msb") (.intLit 128)) (.intLit (2 ^ (64 : Nat)))) ])
      (.ok { contract := contract v, locals := getTickStoreAfterLog2BaseLet I } evm) := by
  change ExecBlock (config v) { contract := contract v, locals := getTickStoreWithMsb I } evm
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
                (shlE (.var "ratio") (subE (.intLit 127) (.var "msb"))) ] ]) ++
        [ .letDecl "log_2" (some int256)
            (mulE (subE (.var "msb") (.intLit 128)) (.intLit (2 ^ (64 : Nat)))) ])
      (.ok { contract := contract v, locals := getTickStoreAfterLog2BaseLet I } evm)
  exact execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceThroughNormalizeR evm I)
    (uniswapV3PoolGetTickAtSqrtRatioSourceLog2BaseLet evm I)

end Benchmarks.UniswapV3Pool

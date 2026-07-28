import Benchmarks.UniswapV3Pool.InitializeSourceGetTickLogStep62

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

def getTickSourceLogStepRShiftedNat (r : Nat) : Nat :=
  r * r / 2 ^ (127 : Nat)

def getTickSourceLogStepRShiftedValue (r : Nat) : Value :=
  .int (getTickSourceLogStepRShiftedNat r)

def getTickSourceLogStepStoreAfterRShifted (S : Store) (r : Nat) : Store :=
  S.insert "r" (getTickSourceLogStepRShiftedValue r)

def getTickSourceLogStepFNat (r : Nat) : Nat :=
  getTickSourceLogStepRShiftedNat r / 2 ^ (128 : Nat)

def getTickSourceLogStepFValue (r : Nat) : Value :=
  .int (getTickSourceLogStepFNat r)

def getTickSourceLogStepStoreAfterFLet (S : Store) (r : Nat) : Store :=
  (getTickSourceLogStepStoreAfterRShifted S r).insert "f" (getTickSourceLogStepFValue r)

def getTickSourceLogStepLog2AfterInt (log2 : Int) (r bit : Nat) : Int :=
  log2 + (getTickSourceLogStepFNat r : Int) * (2 ^ bit : Int)

def getTickSourceLogStepLog2AfterValue (log2 : Int) (r bit : Nat) : Value :=
  .int (getTickSourceLogStepLog2AfterInt log2 r bit)

def getTickSourceLogStepStoreAfterLog2 (S : Store) (log2 : Int) (r bit : Nat) : Store :=
  (getTickSourceLogStepStoreAfterFLet S r).insert "log_2"
    (getTickSourceLogStepLog2AfterValue log2 r bit)

def getTickSourceLogStepRAfterNat (r : Nat) : Nat :=
  getTickSourceLogStepRShiftedNat r / 2 ^ getTickSourceLogStepFNat r

def getTickSourceLogStepRAfterValue (r : Nat) : Value :=
  .int (getTickSourceLogStepRAfterNat r)

def getTickSourceLogStepStoreAfter (S : Store) (log2 : Int) (r bit : Nat) : Store :=
  (getTickSourceLogStepStoreAfterLog2 S log2 r bit).insert "r"
    (getTickSourceLogStepRAfterValue r)

theorem getTickSourceLogStepRShiftedNat_lt_wordModulus (r : Nat)
    (hr : r * r < EVM.wordModulus) :
    getTickSourceLogStepRShiftedNat r < EVM.wordModulus := by
  unfold getTickSourceLogStepRShiftedNat
  exact lt_of_le_of_lt (Nat.div_le_self _ _) hr

theorem getTickSourceLogStepRShiftedNat_lt_twoPow129 (r : Nat)
    (hr : r * r < EVM.wordModulus) :
    getTickSourceLogStepRShiftedNat r < 2 ^ (129 : Nat) := by
  unfold getTickSourceLogStepRShiftedNat
  rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ (127 : Nat))]
  rw [← Nat.pow_add]
  norm_num
  exact hr

theorem getTickSourceLogStepFNat_le_1 (r : Nat) (hr : r * r < EVM.wordModulus) :
    getTickSourceLogStepFNat r ≤ 1 := by
  unfold getTickSourceLogStepFNat
  have hshifted := getTickSourceLogStepRShiftedNat_lt_twoPow129 r hr
  have hf : getTickSourceLogStepRShiftedNat r / 2 ^ (128 : Nat) < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ (128 : Nat))]
    norm_num
    exact hshifted
  omega

theorem getTickSourceLogStepRAfterNat_lt_twoPow128 (r : Nat)
    (hr : r * r < EVM.wordModulus) :
    getTickSourceLogStepRAfterNat r < 2 ^ (128 : Nat) := by
  unfold getTickSourceLogStepRAfterNat getTickSourceLogStepFNat
  exact sourceLogStepNextNat_lt_twoPow128
    (getTickSourceLogStepRShiftedNat r)
    (getTickSourceLogStepRShiftedNat_lt_twoPow129 r hr)

theorem getTickSourceLogStepRAfterNat_mul_self_lt_wordModulus (r : Nat)
    (hr : r * r < EVM.wordModulus) :
    getTickSourceLogStepRAfterNat r * getTickSourceLogStepRAfterNat r < EVM.wordModulus := by
  have hrlt := getTickSourceLogStepRAfterNat_lt_twoPow128 r hr
  have hrle : getTickSourceLogStepRAfterNat r ≤ 2 ^ (128 : Nat) - 1 :=
    Nat.le_pred_of_lt hrlt
  have hmul := Nat.mul_le_mul hrle hrle
  exact Nat.lt_of_le_of_lt hmul (by norm_num [EVM.wordModulus, EVM.twoPow])

theorem getTickSourceLogStepStoreAfter_r (S : Store) (log2 : Int) (r bit : Nat) :
    (getTickSourceLogStepStoreAfter S log2 r bit).get? "r" =
      some (getTickSourceLogStepRAfterValue r) := by
  rw [getTickSourceLogStepStoreAfter, store_get_self]

theorem getTickSourceLogStepStoreAfter_log2 (S : Store) (log2 : Int) (r bit : Nat) :
    (getTickSourceLogStepStoreAfter S log2 r bit).get? "log_2" =
      some (getTickSourceLogStepLog2AfterValue log2 r bit) := by
  rw [getTickSourceLogStepStoreAfter]
  rw [store_get_ne (getTickSourceLogStepStoreAfterLog2 S log2 r bit) (k := "r")
    (a := "log_2") (getTickSourceLogStepRAfterValue r) (by decide)]
  rw [getTickSourceLogStepStoreAfterLog2, store_get_self]

theorem getTickSourceLogStepExec {v : PoolImmutables} (evm : EVM.State)
    (S : Store) (log2 : Int) (r bit : Nat)
    (hrget : S.get? "r" = some (Value.int (Int.ofNat r)))
    (hlog2get : S.get? "log_2" = some (Value.int log2))
    (hrmul : r * r < EVM.wordModulus) :
    ExecBlock (config v) { contract := contract v, locals := S } evm (logStep bit true)
      (.ok { contract := contract v, locals := getTickSourceLogStepStoreAfter S log2 r bit }
        evm) := by
  have evalR : evalExpr? (config v) { contract := contract v, locals := S } evm
      (.var "r") = .ok (.int (Int.ofNat r)) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [hrget]
  have evalLog2 : evalExpr? (config v) { contract := contract v, locals := S } evm
      (.var "log_2") = .ok (.int log2) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [hlog2get]
  have evalMul : evalExpr? (config v) { contract := contract v, locals := S } evm
      (mulE (.var "r") (.var "r")) = .ok (.int (Int.ofNat (r * r))) := by
    unfold mulE
    simp only [evalExpr?, evalR, EvalResult.bind, bind, evalBinaryOp?]
    change EvalResult.ok (Value.int ((r : Int) * (r : Int))) =
      EvalResult.ok (Value.int ((r * r : Nat) : Int))
    rw [← Int.natCast_mul]
  have evalRShifted : evalExpr? (config v) { contract := contract v, locals := S } evm
      (shrE (mulE (.var "r") (.var "r")) (.intLit 127)) =
      .ok (getTickSourceLogStepRShiftedValue r) := by
    unfold shrE
    simp only [evalExpr?, evalMul, EvalResult.bind, bind, pure]
    rw [evalBinaryOp_int_shr_ok]
    · rw [getTickSourceLogStepRShiftedValue, getTickSourceLogStepRShiftedNat]
      rw [intOfNat_toNat_div_pow_127_cast]
    · exact Int.natCast_nonneg _
    · exact Int.ofNat_lt.mpr hrmul
    · norm_num
    · norm_num
  have assignRShifted :
      assignStorageRef? (config v) { contract := contract v, locals := S }
        evm .localVar (varRef "r") (getTickSourceLogStepRShiftedValue r) =
        .ok ({ contract := contract v, locals := getTickSourceLogStepStoreAfterRShifted S r },
          evm) := by
    rw [assignStorageRef?]
    rw [varRef]
    rw [hrget]
    simp [getTickSourceLogStepStoreAfterRShifted, updateLocalPath?, pure, bind,
      EvalResult.bind]
  have hShiftedR : (getTickSourceLogStepStoreAfterRShifted S r).get? "r" =
      some (getTickSourceLogStepRShiftedValue r) := by
    rw [getTickSourceLogStepStoreAfterRShifted, store_get_self]
  have hShiftedLog2 : (getTickSourceLogStepStoreAfterRShifted S r).get? "log_2" =
      some (Value.int log2) := by
    rw [getTickSourceLogStepStoreAfterRShifted]
    rw [store_get_ne S (k := "r") (a := "log_2")
      (getTickSourceLogStepRShiftedValue r) (by decide)]
    exact hlog2get
  have evalRShiftedVar : evalExpr? (config v)
      { contract := contract v, locals := getTickSourceLogStepStoreAfterRShifted S r }
      evm (.var "r") = .ok (getTickSourceLogStepRShiftedValue r) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [hShiftedR]
  have evalF : evalExpr? (config v)
      { contract := contract v, locals := getTickSourceLogStepStoreAfterRShifted S r }
      evm (shrE (.var "r") shift128) = .ok (getTickSourceLogStepFValue r) := by
    unfold shrE shift128
    simp only [evalExpr?, evalRShiftedVar, EvalResult.bind, bind, pure]
    change evalBinaryOp? .shr (.int (Int.ofNat (getTickSourceLogStepRShiftedNat r)))
        (.int (Int.ofNat 128)) = .ok (getTickSourceLogStepFValue r)
    rw [evalBinaryOp_int_shr_ok]
    · unfold getTickSourceLogStepFValue getTickSourceLogStepFNat
      rw [intOfNat_toNat_div_pow_cast]
    · exact Int.natCast_nonneg _
    · exact Int.ofNat_lt.mpr (getTickSourceLogStepRShiftedNat_lt_wordModulus r hrmul)
    · norm_num
    · norm_num
  have hAfterFLog2 : (getTickSourceLogStepStoreAfterFLet S r).get? "log_2" =
      some (Value.int log2) := by
    rw [getTickSourceLogStepStoreAfterFLet]
    rw [store_get_ne (getTickSourceLogStepStoreAfterRShifted S r) (k := "f")
      (a := "log_2") (getTickSourceLogStepFValue r) (by decide)]
    exact hShiftedLog2
  have hAfterFR : (getTickSourceLogStepStoreAfterFLet S r).get? "r" =
      some (getTickSourceLogStepRShiftedValue r) := by
    rw [getTickSourceLogStepStoreAfterFLet]
    rw [store_get_ne (getTickSourceLogStepStoreAfterRShifted S r) (k := "f")
      (a := "r") (getTickSourceLogStepFValue r) (by decide)]
    exact hShiftedR
  have hAfterFF : (getTickSourceLogStepStoreAfterFLet S r).get? "f" =
      some (getTickSourceLogStepFValue r) := by
    rw [getTickSourceLogStepStoreAfterFLet, store_get_self]
  have evalLog2AfterF : evalExpr? (config v)
      { contract := contract v, locals := getTickSourceLogStepStoreAfterFLet S r }
      evm (.var "log_2") = .ok (.int log2) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [hAfterFLog2]
  have evalFAfterF : evalExpr? (config v)
      { contract := contract v, locals := getTickSourceLogStepStoreAfterFLet S r }
      evm (.var "f") = .ok (getTickSourceLogStepFValue r) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [hAfterFF]
  have evalLog2Add : evalExpr? (config v)
      { contract := contract v, locals := getTickSourceLogStepStoreAfterFLet S r }
      evm (addE (.var "log_2") (mulE (.var "f") (.intLit (2 ^ bit)))) =
      .ok (getTickSourceLogStepLog2AfterValue log2 r bit) := by
    unfold addE mulE getTickSourceLogStepLog2AfterValue getTickSourceLogStepLog2AfterInt
    simp only [evalExpr?, evalLog2AfterF, evalFAfterF, EvalResult.bind, bind,
      evalBinaryOp?, getTickSourceLogStepFValue]
  have assignLog2 : assignStorageRef? (config v)
      { contract := contract v, locals := getTickSourceLogStepStoreAfterFLet S r }
      evm .localVar (varRef "log_2") (getTickSourceLogStepLog2AfterValue log2 r bit) =
      .ok ({ contract := contract v, locals := getTickSourceLogStepStoreAfterLog2 S log2 r bit },
        evm) := by
    rw [assignStorageRef?]
    rw [varRef]
    rw [hAfterFLog2]
    simp [getTickSourceLogStepStoreAfterLog2, updateLocalPath?, pure, bind,
      EvalResult.bind]
  have hAfterLog2R : (getTickSourceLogStepStoreAfterLog2 S log2 r bit).get? "r" =
      some (getTickSourceLogStepRShiftedValue r) := by
    rw [getTickSourceLogStepStoreAfterLog2]
    rw [store_get_ne (getTickSourceLogStepStoreAfterFLet S r) (k := "log_2")
      (a := "r") (getTickSourceLogStepLog2AfterValue log2 r bit) (by decide)]
    exact hAfterFR
  have hAfterLog2F : (getTickSourceLogStepStoreAfterLog2 S log2 r bit).get? "f" =
      some (getTickSourceLogStepFValue r) := by
    rw [getTickSourceLogStepStoreAfterLog2]
    rw [store_get_ne (getTickSourceLogStepStoreAfterFLet S r) (k := "log_2")
      (a := "f") (getTickSourceLogStepLog2AfterValue log2 r bit) (by decide)]
    exact hAfterFF
  have evalRAfterLog2 : evalExpr? (config v)
      { contract := contract v, locals := getTickSourceLogStepStoreAfterLog2 S log2 r bit }
      evm (.var "r") = .ok (getTickSourceLogStepRShiftedValue r) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [hAfterLog2R]
  have evalFAfterLog2 : evalExpr? (config v)
      { contract := contract v, locals := getTickSourceLogStepStoreAfterLog2 S log2 r bit }
      evm (.var "f") = .ok (getTickSourceLogStepFValue r) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [hAfterLog2F]
  have evalRAfter : evalExpr? (config v)
      { contract := contract v, locals := getTickSourceLogStepStoreAfterLog2 S log2 r bit }
      evm (shrE (.var "r") (.var "f")) = .ok (getTickSourceLogStepRAfterValue r) := by
    unfold shrE
    simp only [evalExpr?, evalRAfterLog2, evalFAfterLog2, EvalResult.bind, bind]
    change evalBinaryOp? .shr (.int (Int.ofNat (getTickSourceLogStepRShiftedNat r)))
        (.int (Int.ofNat (getTickSourceLogStepFNat r))) =
      .ok (getTickSourceLogStepRAfterValue r)
    rw [evalBinaryOp_int_shr_ok]
    · unfold getTickSourceLogStepRAfterValue getTickSourceLogStepRAfterNat
      rw [intOfNat_toNat_div_pow_cast]
    · exact Int.natCast_nonneg _
    · exact Int.ofNat_lt.mpr (getTickSourceLogStepRShiftedNat_lt_wordModulus r hrmul)
    · exact Int.natCast_nonneg _
    · have hle := getTickSourceLogStepFNat_le_1 r hrmul
      have hlt : getTickSourceLogStepFNat r < 256 := by omega
      exact Int.ofNat_lt.mpr hlt
  have assignRAfter : assignStorageRef? (config v)
      { contract := contract v, locals := getTickSourceLogStepStoreAfterLog2 S log2 r bit }
      evm .localVar (varRef "r") (getTickSourceLogStepRAfterValue r) =
      .ok ({ contract := contract v, locals := getTickSourceLogStepStoreAfter S log2 r bit },
        evm) := by
    rw [assignStorageRef?]
    rw [varRef]
    rw [hAfterLog2R]
    simp [getTickSourceLogStepStoreAfter, updateLocalPath?, pure, bind, EvalResult.bind]
  change ExecBlock (config v) { contract := contract v, locals := S } evm
      [ .assign .localVar (varRef "r") (shrE (mulE (.var "r") (.var "r")) (.intLit 127)),
        .letDecl "f" (some uint256) (shrE (.var "r") shift128),
        .assign .localVar (varRef "log_2")
          (addE (.var "log_2") (mulE (.var "f") (.intLit (2 ^ bit)))),
        .assign .localVar (varRef "r") (shrE (.var "r") (.var "f")) ]
      (.ok { contract := contract v, locals := getTickSourceLogStepStoreAfter S log2 r bit } evm)
  refine ExecBlock.consNormal (ExecStmt.assign evalRShifted assignRShifted) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl evalF) ?_
  refine ExecBlock.consNormal (ExecStmt.assign evalLog2Add assignLog2) ?_
  exact ExecBlock.consNormal (ExecStmt.assign evalRAfter assignRAfter) ExecBlock.nil

def getTickSourceLogRShifted61Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogStepRShiftedNat (getTickSourceLogRAfter62Nat I)

def getTickSourceLogF61Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogStepFNat (getTickSourceLogRAfter62Nat I)

def getTickSourceLog2After61Int (I : ExecutionEnv) : Int :=
  getTickSourceLogStepLog2AfterInt (getTickSourceLog2After62Int I)
    (getTickSourceLogRAfter62Nat I) 61

def getTickSourceLogRAfter61Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogStepRAfterNat (getTickSourceLogRAfter62Nat I)

def getTickStoreAfterLogStep61 (I : ExecutionEnv) : Store :=
  getTickSourceLogStepStoreAfter (getTickStoreAfterLogStep62 I)
    (getTickSourceLog2After62Int I) (getTickSourceLogRAfter62Nat I) 61

theorem getTickSourceLogRAfter61Nat_lt_twoPow128 (I : ExecutionEnv) :
    getTickSourceLogRAfter61Nat I < 2 ^ (128 : Nat) := by
  unfold getTickSourceLogRAfter61Nat
  exact getTickSourceLogStepRAfterNat_lt_twoPow128
    (getTickSourceLogRAfter62Nat I)
    (getTickSourceLogRAfter62Nat_mul_self_lt_wordModulus I)

theorem getTickSourceLogRAfter61Nat_mul_self_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceLogRAfter61Nat I * getTickSourceLogRAfter61Nat I < EVM.wordModulus := by
  unfold getTickSourceLogRAfter61Nat
  exact getTickSourceLogStepRAfterNat_mul_self_lt_wordModulus
    (getTickSourceLogRAfter62Nat I)
    (getTickSourceLogRAfter62Nat_mul_self_lt_wordModulus I)

theorem getTickStoreAfterLog2Step62_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLog2Step62 I).get? "log_2" =
      some (getTickSourceLog2After62Value I) := by
  rw [getTickStoreAfterLog2Step62, store_get_self]

theorem getTickStoreAfterLogStep62_r (I : ExecutionEnv) :
    (getTickStoreAfterLogStep62 I).get? "r" = some (getTickSourceLogRAfter62Value I) := by
  rw [getTickStoreAfterLogStep62, store_get_self]

theorem getTickStoreAfterLogStep62_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogStep62 I).get? "log_2" =
      some (getTickSourceLog2After62Value I) := by
  rw [getTickStoreAfterLogStep62]
  rw [store_get_ne (getTickStoreAfterLog2Step62 I) (k := "r") (a := "log_2")
    (getTickSourceLogRAfter62Value I) (by decide)]
  exact getTickStoreAfterLog2Step62_log2 I

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogStep61 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep62 I }
      evm (logStep 61 true)
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep61 I } evm) := by
  exact getTickSourceLogStepExec evm (getTickStoreAfterLogStep62 I)
    (getTickSourceLog2After62Int I) (getTickSourceLogRAfter62Nat I) 61
    (by simpa [getTickSourceLogRAfter62Value] using getTickStoreAfterLogStep62_r I)
    (by simpa [getTickSourceLog2After62Value] using getTickStoreAfterLogStep62_log2 I)
    (getTickSourceLogRAfter62Nat_mul_self_lt_wordModulus I)

theorem uniswapV3PoolGetTickAtSqrtRatioSourceThroughLogStep61 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreWithMsb I } evm
      ((((msbStep 7 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF ++
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
        logStep 62 true) ++
        logStep 61 true)
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep61 I } evm) := by
  exact execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceThroughLogStep62 evm I)
    (uniswapV3PoolGetTickAtSqrtRatioSourceLogStep61 evm I)

end Benchmarks.UniswapV3Pool

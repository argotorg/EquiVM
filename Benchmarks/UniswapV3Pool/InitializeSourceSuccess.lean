import Benchmarks.UniswapV3Pool.InitializeSuccess

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

def initializeObservationEvaledRef (field : Ident) : EvaledStorageRef :=
  { base := "observations", steps := [.aindex (.int 0), .field field] }

theorem evalStorageRef_initializeObservation {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) (field : Ident) :
    evalStorageRef (config v) { contract := contract v, locals := initializeStore I } evm
      (observationsF (.intLit 0) field) = .ok (initializeObservationEvaledRef field) := by
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, observationsF,
    initializeObservationEvaledRef, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    contract, storageDecls, storageTypeAt?, evalExpr?]

theorem initializeObservationBase_zero : observationBase (.int 0) = (⟨8⟩ : UInt256) := by
  unfold observationBase keyValueToWord EVM.wordOfInt
  apply u256_inj
  rfl

abbrev initializeTimeValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (initializeObservationTimestampWord I).toNat)

abbrev initializeTickValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (getTickEstimatedWord I).toNat)

abbrev initializeStoreWithTick (I : ExecutionEnv) : Store :=
  (initializeStore I).insert "tick" (initializeTickValue I)

abbrev initializeStoreWithTickAndTime (I : ExecutionEnv) : Store :=
  (initializeStoreWithTick I).insert "time" (initializeTimeValue I)

def getTickSourceRatioNat (I : ExecutionEnv) : Nat :=
  ((initializeArgWord I).toNat * 2 ^ (32 : Nat)) % EVM.wordModulus

def getTickSourceRatioValue (I : ExecutionEnv) : Value :=
  .int (getTickSourceRatioNat I)

abbrev getTickSourceMsbValue : Value :=
  .int 0

def getTickStoreWithRatio (I : ExecutionEnv) : Store :=
  (initializeStore I).insert "ratio" (getTickSourceRatioValue I)

def getTickStoreWithR (I : ExecutionEnv) : Store :=
  (getTickStoreWithRatio I).insert "r" (getTickSourceRatioValue I)

def getTickStoreWithMsb (I : ExecutionEnv) : Store :=
  (getTickStoreWithR I).insert "msb" getTickSourceMsbValue

theorem evalExpr_getTick_sourceRatio {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := initializeStore I } evm
      (shlE (.var "sqrtPriceX96") shift32) = .ok (getTickSourceRatioValue I) := by
  unfold shlE shift32 getTickSourceRatioValue
  simp only [evalExpr?, uniswapV3PoolInitializeEvalSqrtPriceVar, EvalResult.bind, bind,
    pure, evalBinaryOp?]
  rw [if_pos]
  · rw [if_neg]
    · rw [show Int.toNat 32 = 32 by native_decide]
      rfl
    · norm_num
  · constructor
    · exact Int.natCast_nonneg _
    · constructor
      · exact Int.ofNat_lt.mpr (initializeArgWord I).val.isLt
      · norm_num [EVM.wordModulus]

theorem getTickSourceRatioNat_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceRatioNat I < EVM.wordModulus := by
  exact Nat.mod_lt _ (by native_decide)

theorem getTickStoreWithRatio_ratio (I : ExecutionEnv) :
    (getTickStoreWithRatio I).get? "ratio" = some (getTickSourceRatioValue I) :=
  store_get_self (initializeStore I) "ratio" (getTickSourceRatioValue I)

theorem evalExpr_getTick_ratioVar {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreWithRatio I }
      evm (.var "ratio") = .ok (getTickSourceRatioValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreWithRatio_ratio]

theorem uniswapV3PoolGetTickAtSqrtRatioSourcePrefix {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342) :
    ExecBlock (config v) { contract := contract v, locals := initializeStore I } evm
      [ .require (andE (geE (.var "sqrtPriceX96") minSqrtRatio)
          (ltE (.var "sqrtPriceX96") maxSqrtRatio)),
        .letDecl "ratio" (some uint256) (shlE (.var "sqrtPriceX96") shift32),
        .letDecl "r" (some uint256) (.var "ratio"),
        .letDecl "msb" (some uint256) (.intLit 0) ]
      (.ok { contract := contract v, locals := getTickStoreWithMsb I } evm) := by
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (uniswapV3PoolGetTickAtSqrtRatioEvalRangeTrue (v := v) (evm := evm) (I := I)
        hlo hhi)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_getTick_sourceRatio evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_getTick_ratioVar evm I)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.letDecl (by simp [evalExpr?, getTickSourceMsbValue, pure]))
    ExecBlock.nil

def getTickSourceRatioGt7 (I : ExecutionEnv) : Bool :=
  decide (getTickSourceRatioNat I > 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)

def getTickSourceMsbF7Nat (I : ExecutionEnv) : Nat :=
  if getTickSourceRatioGt7 I then 2 ^ (7 : Nat) else 0

def getTickSourceMsbF7Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceMsbF7Nat I)

def getTickStoreAfterF7Let (I : ExecutionEnv) : Store :=
  (getTickStoreWithMsb I).insert "f" (getTickSourceMsbF7Value I)

def getTickSourceMsbAfter7Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceMsbF7Nat I)

def getTickStoreAfterMsb7 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterF7Let I).insert "msb" (getTickSourceMsbAfter7Value I)

def getTickSourceRAfterMsb7Nat (I : ExecutionEnv) : Nat :=
  getTickSourceRatioNat I / 2 ^ getTickSourceMsbF7Nat I

def getTickSourceRAfterMsb7Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceRAfterMsb7Nat I)

def getTickStoreAfterMsbStep7 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterMsb7 I).insert "r" (getTickSourceRAfterMsb7Value I)

theorem getTickStoreWithMsb_r (I : ExecutionEnv) :
    (getTickStoreWithMsb I).get? "r" = some (getTickSourceRatioValue I) := by
  rw [getTickStoreWithMsb]
  rw [store_get_ne (getTickStoreWithR I) (k := "msb") (a := "r")
    getTickSourceMsbValue (by decide)]
  rw [getTickStoreWithR, store_get_self]

theorem getTickStoreWithMsb_msb (I : ExecutionEnv) :
    (getTickStoreWithMsb I).get? "msb" = some getTickSourceMsbValue := by
  rw [getTickStoreWithMsb, store_get_self]

theorem evalExpr_getTick_rVar_withMsb {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreWithMsb I }
      evm (.var "r") = .ok (getTickSourceRatioValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreWithMsb_r]

theorem evalExpr_getTick_msbVar_withMsb {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreWithMsb I }
      evm (.var "msb") = .ok getTickSourceMsbValue := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreWithMsb_msb]

theorem evalBinaryOp_getTick_ratioGt7 (I : ExecutionEnv) :
    evalBinaryOp? .gt (getTickSourceRatioValue I)
      (.int 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) =
    .ok (.bool (getTickSourceRatioGt7 I)) := by
  unfold getTickSourceRatioValue getTickSourceRatioGt7
  simp only [evalBinaryOp?]
  by_cases h : getTickSourceRatioNat I > 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  · have hInt : ((getTickSourceRatioNat I : Nat) : Int) >
        (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF : Int) := by omega
    rw [decide_eq_true hInt, decide_eq_true h]
  · have hInt : ¬(((getTickSourceRatioNat I : Nat) : Int) >
        (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF : Int)) := by omega
    rw [decide_eq_false hInt, decide_eq_false h]

theorem evalExpr_getTick_msbF7 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreWithMsb I } evm
      (.ite (gtE (.var "r") (.intLit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF))
        (.intLit (2 ^ (7 : Nat))) (.intLit 0)) =
      .ok (getTickSourceMsbF7Value I) := by
  unfold gtE getTickSourceMsbF7Value getTickSourceMsbF7Nat
  simp only [evalExpr?, evalExpr_getTick_rVar_withMsb, EvalResult.bind, bind, pure]
  rw [evalBinaryOp_getTick_ratioGt7]
  cases getTickSourceRatioGt7 I <;> rfl

theorem getTickSourceMsbF7Nat_le_128 (I : ExecutionEnv) :
    getTickSourceMsbF7Nat I ≤ 128 := by
  unfold getTickSourceMsbF7Nat
  split <;> norm_num

theorem getTickStoreAfterF7Let_msb (I : ExecutionEnv) :
    (getTickStoreAfterF7Let I).get? "msb" = some getTickSourceMsbValue := by
  rw [getTickStoreAfterF7Let]
  rw [store_get_ne (getTickStoreWithMsb I) (k := "f") (a := "msb")
    (getTickSourceMsbF7Value I) (by decide)]
  rw [getTickStoreWithMsb, store_get_self]

theorem getTickStoreAfterF7Let_f (I : ExecutionEnv) :
    (getTickStoreAfterF7Let I).get? "f" = some (getTickSourceMsbF7Value I) := by
  rw [getTickStoreAfterF7Let, store_get_self]

theorem evalExpr_getTick_msb_add_f7 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterF7Let I } evm
      (addE (.var "msb") (.var "f")) = .ok (getTickSourceMsbAfter7Value I) := by
  unfold addE getTickSourceMsbAfter7Value
  simp only [evalExpr?, EvalResult.ofOption, getTickStoreAfterF7Let_msb,
    getTickStoreAfterF7Let_f, getTickSourceMsbValue, getTickSourceMsbF7Value,
    EvalResult.bind, bind, evalBinaryOp?]
  simp

theorem assignStorageRef_getTick_msb_afterF7 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterF7Let I }
      evm .localVar (varRef "msb") (getTickSourceMsbAfter7Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterMsb7 I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterF7Let_msb]
  simp [getTickStoreAfterMsb7, updateLocalPath?, pure, bind, EvalResult.bind]

theorem getTickStoreAfterMsb7_r (I : ExecutionEnv) :
    (getTickStoreAfterMsb7 I).get? "r" = some (getTickSourceRatioValue I) := by
  rw [getTickStoreAfterMsb7]
  rw [store_get_ne (getTickStoreAfterF7Let I) (k := "msb") (a := "r")
    (getTickSourceMsbAfter7Value I) (by decide)]
  rw [getTickStoreAfterF7Let]
  rw [store_get_ne (getTickStoreWithMsb I) (k := "f") (a := "r")
    (getTickSourceMsbF7Value I) (by decide)]
  exact getTickStoreWithMsb_r I

theorem getTickStoreAfterMsb7_f (I : ExecutionEnv) :
    (getTickStoreAfterMsb7 I).get? "f" = some (getTickSourceMsbF7Value I) := by
  rw [getTickStoreAfterMsb7]
  rw [store_get_ne (getTickStoreAfterF7Let I) (k := "msb") (a := "f")
    (getTickSourceMsbAfter7Value I) (by decide)]
  exact getTickStoreAfterF7Let_f I

theorem evalExpr_getTick_rVar_afterMsb7 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb7 I }
      evm (.var "r") = .ok (getTickSourceRatioValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsb7_r]

theorem evalExpr_getTick_fVar_afterMsb7 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb7 I }
      evm (.var "f") = .ok (getTickSourceMsbF7Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsb7_f]

-- LIBRARY CANDIDATE: generic successful evaluation for Solm integer `SHR`.
theorem evalBinaryOp_int_shr_ok {x s : Int}
    (hx0 : 0 ≤ x) (hxlt : x < (EVM.wordModulus : Int))
    (hs0 : 0 ≤ s) (hslt : s < 256) :
    evalBinaryOp? .shr (.int x) (.int s) = .ok (.int (x.toNat / 2 ^ s.toNat)) := by
  simp only [evalBinaryOp?]
  rw [if_pos ⟨hx0, hxlt, hs0⟩]
  rw [if_neg (not_le.mpr hslt)]

theorem intOfNat_toNat_div_pow (n s : Nat) :
    (Int.ofNat n).toNat / 2 ^ (Int.ofNat s).toNat = n / 2 ^ s := by
  rfl

theorem intOfNat_toNat_div_pow_cast (n s : Nat) :
    ((Int.ofNat n).toNat / 2 ^ (Int.ofNat s).toNat : Int) =
      (n / 2 ^ s : Nat) := by
  rfl

theorem evalExpr_getTick_r_shr_f7 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb7 I } evm
      (shrE (.var "r") (.var "f")) = .ok (getTickSourceRAfterMsb7Value I) := by
  unfold shrE
  simp only [evalExpr?, evalExpr_getTick_rVar_afterMsb7,
    evalExpr_getTick_fVar_afterMsb7, EvalResult.bind, bind]
  change evalBinaryOp? .shr (.int (Int.ofNat (getTickSourceRatioNat I)))
      (.int (Int.ofNat (getTickSourceMsbF7Nat I))) =
    .ok (getTickSourceRAfterMsb7Value I)
  rw [evalBinaryOp_int_shr_ok]
  · unfold getTickSourceRAfterMsb7Value getTickSourceRAfterMsb7Nat
    rw [intOfNat_toNat_div_pow_cast]
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_lt.mpr (getTickSourceRatioNat_lt_wordModulus I)
  · exact Int.natCast_nonneg _
  · have hle := getTickSourceMsbF7Nat_le_128 I
    have hltNat : getTickSourceMsbF7Nat I < 256 := by omega
    exact Int.ofNat_lt.mpr hltNat

theorem uniswapV3PoolGetTickAtSqrtRatioSourceMsbStep7Prefix {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreWithMsb I } evm
      [ .letDecl "f" (some uint256)
          (.ite (gtE (.var "r") (.intLit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF))
            (.intLit (2 ^ (7 : Nat))) (.intLit 0)),
        .assign .localVar (varRef "msb") (addE (.var "msb") (.var "f")) ]
      (.ok { contract := contract v, locals := getTickStoreAfterMsb7 I } evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_getTick_msbF7 evm I)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_msb_add_f7 evm I)
      (assignStorageRef_getTick_msb_afterF7 evm I))
    ExecBlock.nil

theorem assignStorageRef_getTick_r_afterF7 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterMsb7 I }
      evm .localVar (varRef "r") (getTickSourceRAfterMsb7Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterMsbStep7 I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterMsb7_r]
  simp [getTickStoreAfterMsbStep7, updateLocalPath?, pure, bind, EvalResult.bind]

theorem uniswapV3PoolGetTickAtSqrtRatioSourceMsbStep7 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreWithMsb I } evm
      (msbStep 7 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)
      (.ok { contract := contract v, locals := getTickStoreAfterMsbStep7 I } evm) := by
  change ExecBlock (config v) { contract := contract v, locals := getTickStoreWithMsb I } evm
      [ .letDecl "f" (some uint256)
          (.ite (gtE (.var "r") (.intLit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF))
            (.intLit (2 ^ (7 : Nat))) (.intLit 0)),
        .assign .localVar (varRef "msb") (addE (.var "msb") (.var "f")),
        .assign .localVar (varRef "r") (shrE (.var "r") (.var "f")) ]
      (.ok { contract := contract v, locals := getTickStoreAfterMsbStep7 I } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_getTick_msbF7 evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_msb_add_f7 evm I)
      (assignStorageRef_getTick_msb_afterF7 evm I)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_r_shr_f7 evm I)
      (assignStorageRef_getTick_r_afterF7 evm I))
    ExecBlock.nil

def getTickSourceRAfterMsb7Gt6 (I : ExecutionEnv) : Bool :=
  decide (getTickSourceRAfterMsb7Nat I > 0xFFFFFFFFFFFFFFFF)

def getTickSourceMsbF6Nat (I : ExecutionEnv) : Nat :=
  if getTickSourceRAfterMsb7Gt6 I then 2 ^ (6 : Nat) else 0

def getTickSourceMsbF6Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceMsbF6Nat I)

def getTickStoreAfterF6Let (I : ExecutionEnv) : Store :=
  (getTickStoreAfterMsbStep7 I).insert "f" (getTickSourceMsbF6Value I)

def getTickSourceMsbAfter6Nat (I : ExecutionEnv) : Nat :=
  getTickSourceMsbF7Nat I + getTickSourceMsbF6Nat I

def getTickSourceMsbAfter6Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceMsbAfter6Nat I)

def getTickStoreAfterMsb6 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterF6Let I).insert "msb" (getTickSourceMsbAfter6Value I)

def getTickSourceRAfterMsb6Nat (I : ExecutionEnv) : Nat :=
  getTickSourceRAfterMsb7Nat I / 2 ^ getTickSourceMsbF6Nat I

def getTickSourceRAfterMsb6Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceRAfterMsb6Nat I)

def getTickStoreAfterMsbStep6 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterMsb6 I).insert "r" (getTickSourceRAfterMsb6Value I)

theorem getTickSourceRAfterMsb7Nat_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceRAfterMsb7Nat I < EVM.wordModulus := by
  unfold getTickSourceRAfterMsb7Nat
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (getTickSourceRatioNat_lt_wordModulus I)

theorem getTickStoreAfterMsb7_msb (I : ExecutionEnv) :
    (getTickStoreAfterMsb7 I).get? "msb" = some (getTickSourceMsbAfter7Value I) := by
  rw [getTickStoreAfterMsb7, store_get_self]

theorem getTickStoreAfterMsbStep7_r (I : ExecutionEnv) :
    (getTickStoreAfterMsbStep7 I).get? "r" =
      some (getTickSourceRAfterMsb7Value I) := by
  rw [getTickStoreAfterMsbStep7, store_get_self]

theorem getTickStoreAfterMsbStep7_msb (I : ExecutionEnv) :
    (getTickStoreAfterMsbStep7 I).get? "msb" =
      some (getTickSourceMsbAfter7Value I) := by
  rw [getTickStoreAfterMsbStep7]
  rw [store_get_ne (getTickStoreAfterMsb7 I) (k := "r") (a := "msb")
    (getTickSourceRAfterMsb7Value I) (by decide)]
  exact getTickStoreAfterMsb7_msb I

theorem evalExpr_getTick_rVar_afterMsbStep7 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbStep7 I }
      evm (.var "r") = .ok (getTickSourceRAfterMsb7Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsbStep7_r]

theorem evalExpr_getTick_msbVar_afterMsbStep7 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbStep7 I }
      evm (.var "msb") = .ok (getTickSourceMsbAfter7Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsbStep7_msb]

theorem evalBinaryOp_getTick_rAfter7Gt6 (I : ExecutionEnv) :
    evalBinaryOp? .gt (getTickSourceRAfterMsb7Value I)
      (.int 0xFFFFFFFFFFFFFFFF) =
    .ok (.bool (getTickSourceRAfterMsb7Gt6 I)) := by
  unfold getTickSourceRAfterMsb7Value getTickSourceRAfterMsb7Gt6
  simp only [evalBinaryOp?]
  by_cases h : getTickSourceRAfterMsb7Nat I > 0xFFFFFFFFFFFFFFFF
  · have hInt : ((getTickSourceRAfterMsb7Nat I : Nat) : Int) >
        (0xFFFFFFFFFFFFFFFF : Int) := by omega
    rw [decide_eq_true hInt, decide_eq_true h]
  · have hInt : ¬(((getTickSourceRAfterMsb7Nat I : Nat) : Int) >
        (0xFFFFFFFFFFFFFFFF : Int)) := by omega
    rw [decide_eq_false hInt, decide_eq_false h]

theorem evalExpr_getTick_msbF6 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbStep7 I } evm
      (.ite (gtE (.var "r") (.intLit 0xFFFFFFFFFFFFFFFF))
        (.intLit (2 ^ (6 : Nat))) (.intLit 0)) =
      .ok (getTickSourceMsbF6Value I) := by
  unfold gtE getTickSourceMsbF6Value getTickSourceMsbF6Nat
  simp only [evalExpr?, evalExpr_getTick_rVar_afterMsbStep7, EvalResult.bind, bind, pure]
  rw [evalBinaryOp_getTick_rAfter7Gt6]
  cases getTickSourceRAfterMsb7Gt6 I <;> rfl

theorem getTickSourceMsbF6Nat_le_64 (I : ExecutionEnv) :
    getTickSourceMsbF6Nat I ≤ 64 := by
  unfold getTickSourceMsbF6Nat
  split <;> norm_num

theorem getTickStoreAfterF6Let_msb (I : ExecutionEnv) :
    (getTickStoreAfterF6Let I).get? "msb" = some (getTickSourceMsbAfter7Value I) := by
  rw [getTickStoreAfterF6Let]
  rw [store_get_ne (getTickStoreAfterMsbStep7 I) (k := "f") (a := "msb")
    (getTickSourceMsbF6Value I) (by decide)]
  exact getTickStoreAfterMsbStep7_msb I

theorem getTickStoreAfterF6Let_f (I : ExecutionEnv) :
    (getTickStoreAfterF6Let I).get? "f" = some (getTickSourceMsbF6Value I) := by
  rw [getTickStoreAfterF6Let, store_get_self]

theorem evalExpr_getTick_msb_add_f6 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterF6Let I } evm
      (addE (.var "msb") (.var "f")) = .ok (getTickSourceMsbAfter6Value I) := by
  unfold addE getTickSourceMsbAfter6Value
    getTickSourceMsbAfter6Nat
  simp only [evalExpr?, EvalResult.ofOption, getTickStoreAfterF6Let_msb,
    getTickStoreAfterF6Let_f, getTickSourceMsbAfter7Value, getTickSourceMsbF6Value,
    EvalResult.bind, bind, evalBinaryOp?]
  rw [(Nat.cast_add (getTickSourceMsbF7Nat I) (getTickSourceMsbF6Nat I)).symm]

theorem assignStorageRef_getTick_msb_afterF6 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterF6Let I }
      evm .localVar (varRef "msb") (getTickSourceMsbAfter6Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterMsb6 I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterF6Let_msb]
  simp [getTickStoreAfterMsb6, updateLocalPath?, pure, bind, EvalResult.bind]

theorem getTickStoreAfterMsb6_r (I : ExecutionEnv) :
    (getTickStoreAfterMsb6 I).get? "r" = some (getTickSourceRAfterMsb7Value I) := by
  rw [getTickStoreAfterMsb6]
  rw [store_get_ne (getTickStoreAfterF6Let I) (k := "msb") (a := "r")
    (getTickSourceMsbAfter6Value I) (by decide)]
  rw [getTickStoreAfterF6Let]
  rw [store_get_ne (getTickStoreAfterMsbStep7 I) (k := "f") (a := "r")
    (getTickSourceMsbF6Value I) (by decide)]
  exact getTickStoreAfterMsbStep7_r I

theorem getTickStoreAfterMsb6_f (I : ExecutionEnv) :
    (getTickStoreAfterMsb6 I).get? "f" = some (getTickSourceMsbF6Value I) := by
  rw [getTickStoreAfterMsb6]
  rw [store_get_ne (getTickStoreAfterF6Let I) (k := "msb") (a := "f")
    (getTickSourceMsbAfter6Value I) (by decide)]
  exact getTickStoreAfterF6Let_f I

theorem evalExpr_getTick_rVar_afterMsb6 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb6 I }
      evm (.var "r") = .ok (getTickSourceRAfterMsb7Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsb6_r]

theorem evalExpr_getTick_fVar_afterMsb6 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb6 I }
      evm (.var "f") = .ok (getTickSourceMsbF6Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsb6_f]

theorem evalExpr_getTick_r_shr_f6 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb6 I } evm
      (shrE (.var "r") (.var "f")) = .ok (getTickSourceRAfterMsb6Value I) := by
  unfold shrE
  simp only [evalExpr?, evalExpr_getTick_rVar_afterMsb6,
    evalExpr_getTick_fVar_afterMsb6, EvalResult.bind, bind]
  change evalBinaryOp? .shr (.int (Int.ofNat (getTickSourceRAfterMsb7Nat I)))
      (.int (Int.ofNat (getTickSourceMsbF6Nat I))) =
    .ok (getTickSourceRAfterMsb6Value I)
  rw [evalBinaryOp_int_shr_ok]
  · unfold getTickSourceRAfterMsb6Value getTickSourceRAfterMsb6Nat
    rw [intOfNat_toNat_div_pow_cast]
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_lt.mpr (getTickSourceRAfterMsb7Nat_lt_wordModulus I)
  · exact Int.natCast_nonneg _
  · have hle := getTickSourceMsbF6Nat_le_64 I
    have hltNat : getTickSourceMsbF6Nat I < 256 := by omega
    exact Int.ofNat_lt.mpr hltNat

theorem assignStorageRef_getTick_r_afterF6 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterMsb6 I }
      evm .localVar (varRef "r") (getTickSourceRAfterMsb6Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterMsbStep6 I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterMsb6_r]
  simp [getTickStoreAfterMsbStep6, updateLocalPath?, pure, bind, EvalResult.bind]

theorem uniswapV3PoolGetTickAtSqrtRatioSourceMsbStep6 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterMsbStep7 I } evm
      (msbStep 6 0xFFFFFFFFFFFFFFFF)
      (.ok { contract := contract v, locals := getTickStoreAfterMsbStep6 I } evm) := by
  change ExecBlock (config v)
      { contract := contract v, locals := getTickStoreAfterMsbStep7 I } evm
      [ .letDecl "f" (some uint256)
          (.ite (gtE (.var "r") (.intLit 0xFFFFFFFFFFFFFFFF))
            (.intLit (2 ^ (6 : Nat))) (.intLit 0)),
        .assign .localVar (varRef "msb") (addE (.var "msb") (.var "f")),
        .assign .localVar (varRef "r") (shrE (.var "r") (.var "f")) ]
      (.ok { contract := contract v, locals := getTickStoreAfterMsbStep6 I } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_getTick_msbF6 evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_msb_add_f6 evm I)
      (assignStorageRef_getTick_msb_afterF6 evm I)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_r_shr_f6 evm I)
      (assignStorageRef_getTick_r_afterF6 evm I))
    ExecBlock.nil

theorem uniswapV3PoolGetTickAtSqrtRatioSourceMsbSteps76 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreWithMsb I } evm
      (msbStep 7 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF ++
        msbStep 6 0xFFFFFFFFFFFFFFFF)
      (.ok { contract := contract v, locals := getTickStoreAfterMsbStep6 I } evm) := by
  exact execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceMsbStep7 evm I)
    (uniswapV3PoolGetTickAtSqrtRatioSourceMsbStep6 evm I)

def getTickSourceRAfterMsb6Gt5 (I : ExecutionEnv) : Bool :=
  decide (getTickSourceRAfterMsb6Nat I > 0xFFFFFFFF)

def getTickSourceMsbF5Nat (I : ExecutionEnv) : Nat :=
  if getTickSourceRAfterMsb6Gt5 I then 2 ^ (5 : Nat) else 0

def getTickSourceMsbF5Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceMsbF5Nat I)

def getTickStoreAfterF5Let (I : ExecutionEnv) : Store :=
  (getTickStoreAfterMsbStep6 I).insert "f" (getTickSourceMsbF5Value I)

def getTickSourceMsbAfter5Nat (I : ExecutionEnv) : Nat :=
  getTickSourceMsbAfter6Nat I + getTickSourceMsbF5Nat I

def getTickSourceMsbAfter5Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceMsbAfter5Nat I)

def getTickStoreAfterMsb5 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterF5Let I).insert "msb" (getTickSourceMsbAfter5Value I)

def getTickSourceRAfterMsb5Nat (I : ExecutionEnv) : Nat :=
  getTickSourceRAfterMsb6Nat I / 2 ^ getTickSourceMsbF5Nat I

def getTickSourceRAfterMsb5Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceRAfterMsb5Nat I)

def getTickStoreAfterMsbStep5 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterMsb5 I).insert "r" (getTickSourceRAfterMsb5Value I)

theorem getTickSourceRAfterMsb6Nat_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceRAfterMsb6Nat I < EVM.wordModulus := by
  unfold getTickSourceRAfterMsb6Nat
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (getTickSourceRAfterMsb7Nat_lt_wordModulus I)

theorem getTickStoreAfterMsb6_msb (I : ExecutionEnv) :
    (getTickStoreAfterMsb6 I).get? "msb" = some (getTickSourceMsbAfter6Value I) := by
  rw [getTickStoreAfterMsb6, store_get_self]

theorem getTickStoreAfterMsbStep6_r (I : ExecutionEnv) :
    (getTickStoreAfterMsbStep6 I).get? "r" =
      some (getTickSourceRAfterMsb6Value I) := by
  rw [getTickStoreAfterMsbStep6, store_get_self]

theorem getTickStoreAfterMsbStep6_msb (I : ExecutionEnv) :
    (getTickStoreAfterMsbStep6 I).get? "msb" =
      some (getTickSourceMsbAfter6Value I) := by
  rw [getTickStoreAfterMsbStep6]
  rw [store_get_ne (getTickStoreAfterMsb6 I) (k := "r") (a := "msb")
    (getTickSourceRAfterMsb6Value I) (by decide)]
  exact getTickStoreAfterMsb6_msb I

theorem evalExpr_getTick_rVar_afterMsbStep6 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbStep6 I }
      evm (.var "r") = .ok (getTickSourceRAfterMsb6Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsbStep6_r]

theorem evalExpr_getTick_msbVar_afterMsbStep6 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbStep6 I }
      evm (.var "msb") = .ok (getTickSourceMsbAfter6Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsbStep6_msb]

theorem evalBinaryOp_getTick_rAfter6Gt5 (I : ExecutionEnv) :
    evalBinaryOp? .gt (getTickSourceRAfterMsb6Value I)
      (.int 0xFFFFFFFF) =
    .ok (.bool (getTickSourceRAfterMsb6Gt5 I)) := by
  unfold getTickSourceRAfterMsb6Value getTickSourceRAfterMsb6Gt5
  simp only [evalBinaryOp?]
  by_cases h : getTickSourceRAfterMsb6Nat I > 0xFFFFFFFF
  · have hInt : ((getTickSourceRAfterMsb6Nat I : Nat) : Int) >
        (0xFFFFFFFF : Int) := by omega
    rw [decide_eq_true hInt, decide_eq_true h]
  · have hInt : ¬(((getTickSourceRAfterMsb6Nat I : Nat) : Int) >
        (0xFFFFFFFF : Int)) := by omega
    rw [decide_eq_false hInt, decide_eq_false h]

theorem evalExpr_getTick_msbF5 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsbStep6 I } evm
      (.ite (gtE (.var "r") (.intLit 0xFFFFFFFF))
        (.intLit (2 ^ (5 : Nat))) (.intLit 0)) =
      .ok (getTickSourceMsbF5Value I) := by
  unfold gtE getTickSourceMsbF5Value getTickSourceMsbF5Nat
  simp only [evalExpr?, evalExpr_getTick_rVar_afterMsbStep6, EvalResult.bind, bind, pure]
  rw [evalBinaryOp_getTick_rAfter6Gt5]
  cases getTickSourceRAfterMsb6Gt5 I <;> rfl

theorem getTickSourceMsbF5Nat_le_32 (I : ExecutionEnv) :
    getTickSourceMsbF5Nat I ≤ 32 := by
  unfold getTickSourceMsbF5Nat
  split <;> norm_num

theorem getTickStoreAfterF5Let_msb (I : ExecutionEnv) :
    (getTickStoreAfterF5Let I).get? "msb" = some (getTickSourceMsbAfter6Value I) := by
  rw [getTickStoreAfterF5Let]
  rw [store_get_ne (getTickStoreAfterMsbStep6 I) (k := "f") (a := "msb")
    (getTickSourceMsbF5Value I) (by decide)]
  exact getTickStoreAfterMsbStep6_msb I

theorem getTickStoreAfterF5Let_f (I : ExecutionEnv) :
    (getTickStoreAfterF5Let I).get? "f" = some (getTickSourceMsbF5Value I) := by
  rw [getTickStoreAfterF5Let, store_get_self]

theorem evalExpr_getTick_msb_add_f5 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterF5Let I } evm
      (addE (.var "msb") (.var "f")) = .ok (getTickSourceMsbAfter5Value I) := by
  unfold addE getTickSourceMsbAfter5Value
    getTickSourceMsbAfter5Nat
  simp only [evalExpr?, EvalResult.ofOption, getTickStoreAfterF5Let_msb,
    getTickStoreAfterF5Let_f, getTickSourceMsbAfter6Value, getTickSourceMsbF5Value,
    EvalResult.bind, bind, evalBinaryOp?]
  rw [(Nat.cast_add (getTickSourceMsbAfter6Nat I) (getTickSourceMsbF5Nat I)).symm]

theorem assignStorageRef_getTick_msb_afterF5 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterF5Let I }
      evm .localVar (varRef "msb") (getTickSourceMsbAfter5Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterMsb5 I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterF5Let_msb]
  simp [getTickStoreAfterMsb5, updateLocalPath?, pure, bind, EvalResult.bind]

theorem getTickStoreAfterMsb5_r (I : ExecutionEnv) :
    (getTickStoreAfterMsb5 I).get? "r" = some (getTickSourceRAfterMsb6Value I) := by
  rw [getTickStoreAfterMsb5]
  rw [store_get_ne (getTickStoreAfterF5Let I) (k := "msb") (a := "r")
    (getTickSourceMsbAfter5Value I) (by decide)]
  rw [getTickStoreAfterF5Let]
  rw [store_get_ne (getTickStoreAfterMsbStep6 I) (k := "f") (a := "r")
    (getTickSourceMsbF5Value I) (by decide)]
  exact getTickStoreAfterMsbStep6_r I

theorem getTickStoreAfterMsb5_f (I : ExecutionEnv) :
    (getTickStoreAfterMsb5 I).get? "f" = some (getTickSourceMsbF5Value I) := by
  rw [getTickStoreAfterMsb5]
  rw [store_get_ne (getTickStoreAfterF5Let I) (k := "msb") (a := "f")
    (getTickSourceMsbAfter5Value I) (by decide)]
  exact getTickStoreAfterF5Let_f I

theorem evalExpr_getTick_rVar_afterMsb5 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb5 I }
      evm (.var "r") = .ok (getTickSourceRAfterMsb6Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsb5_r]

theorem evalExpr_getTick_fVar_afterMsb5 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb5 I }
      evm (.var "f") = .ok (getTickSourceMsbF5Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterMsb5_f]

theorem evalExpr_getTick_r_shr_f5 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterMsb5 I } evm
      (shrE (.var "r") (.var "f")) = .ok (getTickSourceRAfterMsb5Value I) := by
  unfold shrE
  simp only [evalExpr?, evalExpr_getTick_rVar_afterMsb5,
    evalExpr_getTick_fVar_afterMsb5, EvalResult.bind, bind]
  change evalBinaryOp? .shr (.int (Int.ofNat (getTickSourceRAfterMsb6Nat I)))
      (.int (Int.ofNat (getTickSourceMsbF5Nat I))) =
    .ok (getTickSourceRAfterMsb5Value I)
  rw [evalBinaryOp_int_shr_ok]
  · unfold getTickSourceRAfterMsb5Value getTickSourceRAfterMsb5Nat
    rw [intOfNat_toNat_div_pow_cast]
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_lt.mpr (getTickSourceRAfterMsb6Nat_lt_wordModulus I)
  · exact Int.natCast_nonneg _
  · have hle := getTickSourceMsbF5Nat_le_32 I
    have hltNat : getTickSourceMsbF5Nat I < 256 := by omega
    exact Int.ofNat_lt.mpr hltNat

theorem assignStorageRef_getTick_r_afterF5 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := getTickStoreAfterMsb5 I }
      evm .localVar (varRef "r") (getTickSourceRAfterMsb5Value I) =
      .ok ({ contract := contract v, locals := getTickStoreAfterMsbStep5 I }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [getTickStoreAfterMsb5_r]
  simp [getTickStoreAfterMsbStep5, updateLocalPath?, pure, bind, EvalResult.bind]

theorem uniswapV3PoolGetTickAtSqrtRatioSourceMsbStep5 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterMsbStep6 I } evm
      (msbStep 5 0xFFFFFFFF)
      (.ok { contract := contract v, locals := getTickStoreAfterMsbStep5 I } evm) := by
  change ExecBlock (config v)
      { contract := contract v, locals := getTickStoreAfterMsbStep6 I } evm
      [ .letDecl "f" (some uint256)
          (.ite (gtE (.var "r") (.intLit 0xFFFFFFFF))
            (.intLit (2 ^ (5 : Nat))) (.intLit 0)),
        .assign .localVar (varRef "msb") (addE (.var "msb") (.var "f")),
        .assign .localVar (varRef "r") (shrE (.var "r") (.var "f")) ]
      (.ok { contract := contract v, locals := getTickStoreAfterMsbStep5 I } evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_getTick_msbF5 evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_msb_add_f5 evm I)
      (assignStorageRef_getTick_msb_afterF5 evm I)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_getTick_r_shr_f5 evm I)
      (assignStorageRef_getTick_r_afterF5 evm I))
    ExecBlock.nil

theorem uniswapV3PoolGetTickAtSqrtRatioSourceMsbSteps765 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreWithMsb I } evm
      (msbStep 7 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF ++
        msbStep 6 0xFFFFFFFFFFFFFFFF ++
        msbStep 5 0xFFFFFFFF)
      (.ok { contract := contract v, locals := getTickStoreAfterMsbStep5 I } evm) := by
  exact execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceMsbSteps76 evm I)
    (uniswapV3PoolGetTickAtSqrtRatioSourceMsbStep5 evm I)

def initializeObservationBlockTimestampLoc : StorageLoc :=
  loc ⟨8⟩ ⟨0, by decide⟩ ⟨4, by decide⟩ (by decide) (.int uint32Int)

def initializeObservationTimestampSlotWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor (initializeObservationTimestampWord I)
    (UInt256.land (UInt256.lnot (⟨4294967295⟩ : UInt256))
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩))

def initializeObservationAfterTimestampState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩
    (initializeObservationTimestampSlotWord evm I)

def initializeObservationTickCumulativeLoc : StorageLoc :=
  loc ⟨8⟩ ⟨4, by decide⟩ ⟨7, by decide⟩ (by decide) (.int int56Int)

def initializeObservationAfterTickWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat % 2 ^ 32 +
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat / 2 ^ 88 * 2 ^ 88)

def initializeObservationAfterTickState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩
    (initializeObservationAfterTickWord evm)

def initializeObservationSecondsPerLiquidityLoc : StorageLoc :=
  loc ⟨8⟩ ⟨11, by decide⟩ ⟨20, by decide⟩ (by decide) (.int uint160Int)

def initializeObservationAfterSecondsWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat % 2 ^ 88 +
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat / 2 ^ 248 * 2 ^ 248)

def initializeObservationAfterSecondsState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩
    (initializeObservationAfterSecondsWord evm)

abbrev initializeObservationInitializedLoc : StorageLoc :=
  { slot := ⟨8⟩, offset := ⟨31, by decide⟩, size := ⟨1, by decide⟩,
    hbound := by decide, type := .bool }

theorem initializeObservationTimestampWord_toNat (I : ExecutionEnv) :
    (initializeObservationTimestampWord I).toNat =
      (UInt256.ofNat I.header.timestamp).toNat % 2 ^ 32 := by
  unfold initializeObservationTimestampWord
  rw [u256_land_toNat]
  have hmask32 : (⟨4294967295⟩ : UInt256).toNat = 2 ^ 32 - 1 := by native_decide
  rw [hmask32, nat_land_comm, nat_land_mask_eq_mod]
  rw [Nat.mod_eq_of_lt (by
    exact lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 32)) (by norm_num [UInt256.size]))]

theorem evalExpr_initializeTime {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hEnv : evm.executionEnv = I) :
    evalExpr? (config v) { contract := contract v, locals := initializeStore I } evm
      (modE (.env .timestamp) uint32Modulus) = .ok (initializeTimeValue I) := by
  unfold modE uint32Modulus initializeTimeValue
  simp only [evalExpr?, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hEnv]
  rw [initializeObservationTimestampWord_toNat]
  norm_num

theorem evalExpr_initializeTimeVar {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := initializeStoreWithTickAndTime I }
      evm (.var "time") = .ok (initializeTimeValue I) := by
  simp [evalExpr?, initializeStoreWithTickAndTime, EvalResult.ofOption]

theorem evalExpr_initializeTime_withTick {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) (hEnv : evm.executionEnv = I) :
    evalExpr? (config v) { contract := contract v, locals := initializeStoreWithTick I } evm
      (modE (.env .timestamp) uint32Modulus) = .ok (initializeTimeValue I) := by
  unfold modE uint32Modulus initializeTimeValue
  simp only [evalExpr?, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hEnv]
  rw [initializeObservationTimestampWord_toNat]
  norm_num

theorem evalStorageRef_initializeObservation_withTickAndTime {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) (field : Ident) :
    evalStorageRef (config v) { contract := contract v, locals := initializeStoreWithTickAndTime I }
      evm (observationsF (.intLit 0) field) = .ok (initializeObservationEvaledRef field) := by
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, observationsF,
    initializeObservationEvaledRef, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    contract, storageDecls, storageTypeAt?, evalExpr?]

theorem initializeObservationTimestampWord_lt_twoPow32 (I : ExecutionEnv) :
    (initializeObservationTimestampWord I).toNat < 2 ^ 32 := by
  rw [initializeObservationTimestampWord_toNat]
  exact Nat.mod_lt _ (by norm_num)

private theorem initializeObservationLow32_insert_toNat (low old : UInt256)
    (hlow : low.toNat < 2 ^ 32) :
    (UInt256.lor low (UInt256.land (UInt256.lnot (⟨4294967295⟩ : UInt256)) old)).toNat =
      low.toNat + old.toNat / 2 ^ 32 * 2 ^ 32 := by
  rw [u256_lor_toNat]
  have hclearMask : UInt256.lnot (⟨4294967295⟩ : UInt256) =
      UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 32) := by
    native_decide
  have hhigh :
      (UInt256.land (UInt256.lnot (⟨4294967295⟩ : UInt256)) old).toNat =
        old.toNat / 2 ^ 32 * 2 ^ 32 := by
    rw [hclearMask]
    exact u256_land_high_mask_toNat old 32 (by norm_num)
  have hq : old.toNat / 2 ^ 32 < 2 ^ 224 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 32 * 2 ^ 224 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change old.val.val < 2 ^ 256
    simp [UInt256.size]
  have hlorLt :
      Nat.lor low.toNat
          ((UInt256.land (UInt256.lnot (⟨4294967295⟩ : UInt256)) old).toNat) <
        UInt256.size := by
    rw [hhigh]
    rw [nat_lor_shift_add low.toNat (old.toNat / 2 ^ 32) 32 hlow]
    have hqle : old.toNat / 2 ^ 32 ≤ 2 ^ 224 - 1 := Nat.le_pred_of_lt hq
    have hprod : (old.toNat / 2 ^ 32) * 2 ^ 32 ≤ (2 ^ 224 - 1) * 2 ^ 32 := by
      exact Nat.mul_le_mul_right _ hqle
    norm_num [UInt256.size, Nat.pow_add] at hprod ⊢
    omega
  rw [Nat.mod_eq_of_lt hlorLt]
  rw [hhigh]
  exact nat_lor_shift_add low.toNat (old.toNat / 2 ^ 32) 32 hlow

theorem storageLocStore_initializeObservation_timestamp (evm : EVM.State) (I : ExecutionEnv) :
    storageLocStore evm initializeObservationBlockTimestampLoc (initializeTimeValue I) =
      some (initializeObservationAfterTimestampState evm I) := by
  unfold storageLocStore storageLocWriteWord initializeObservationBlockTimestampLoc
    initializeObservationAfterTimestampState initializeObservationTimestampSlotWord initializeTimeValue loc
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind]
  apply congrArg some
  apply congrArg (fun w : UInt256 => Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ w)
  apply u256_inj
  rw [initializeObservationLow32_insert_toNat]
  · change fromBytes'
        (List.take 0 ↑(EVM.Word.toBytesLEWithSizeProof
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)) ++
          List.take 4 ↑(EVM.Word.toBytesLEWithSizeProof (initializeObservationTimestampWord I)) ++
            List.drop (0 + 4) ↑(EVM.Word.toBytesLEWithSizeProof
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩))) =
        (initializeObservationTimestampWord I).toNat +
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat / 2 ^ 32 * 2 ^ 32
    rw [List.take_zero, List.nil_append]
    rw [fromBytes'_append, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
    simp only [(EVM.Word.toBytesLEWithSizeProof (initializeObservationTimestampWord I)).2,
      List.length_take]
    rw [show min 4 32 = 4 by norm_num]
    rw [show 256 ^ 4 = 2 ^ 32 by norm_num]
    rw [Nat.mod_eq_of_lt (initializeObservationTimestampWord_lt_twoPow32 I)]
    ring
  · exact initializeObservationTimestampWord_lt_twoPow32 I

theorem assignStorageRef_initializeObservation_blockTimestamp {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? (config v)
        { contract := contract v, locals := initializeStoreWithTickAndTime I }
        evm .storage (observationsF (.intLit 0) "blockTimestamp") (initializeTimeValue I) =
      .ok ({ contract := contract v, locals := initializeStoreWithTickAndTime I },
        initializeObservationAfterTimestampState evm I) := by
  apply assignStorageRef_storage_scalar_value
      (er := initializeObservationEvaledRef "blockTimestamp")
      (ty := .elem (.int uint32Int))
      (loc := initializeObservationBlockTimestampLoc)
  · simp [observationsF, initializeStoreWithTickAndTime, initializeStoreWithTick,
      initializeStore]
  · exact evalStorageRef_initializeObservation_withTickAndTime evm I "blockTimestamp"
  · simp [contract, storageDecls, storageTypeAt?, initializeObservationEvaledRef,
      observationStructTy, uint32St]
    native_decide
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      initializeObservationEvaledRef, initializeObservationBlockTimestampLoc, loc,
      initializeObservationBase_zero]
  · trivial
  · exact storageLocStore_initializeObservation_timestamp evm I

theorem initializeObservationAfterTickWord_nat_lt (evm : EVM.State) :
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat % 2 ^ 32 +
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat / 2 ^ 88 * 2 ^ 88 <
      UInt256.size := by
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩
  have hlow : w.toNat % 2 ^ 32 ≤ 2 ^ 32 - 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
  have hhighLt : w.toNat / 2 ^ 88 < 2 ^ 168 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 88 * 2 ^ 168 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change w.val.val < UInt256.size
    exact w.val.isLt
  have hhigh : w.toNat / 2 ^ 88 ≤ 2 ^ 168 - 1 := Nat.le_pred_of_lt hhighLt
  have hmax : (2 ^ 32 - 1) + (2 ^ 168 - 1) * 2 ^ 88 < UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  dsimp [w] at hlow hhigh
  omega

theorem storageLocStore_initializeObservation_tick_zero (evm : EVM.State) :
    storageLocStore evm initializeObservationTickCumulativeLoc (.int 0) =
      some (initializeObservationAfterTickState evm) := by
  unfold storageLocStore storageLocWriteWord initializeObservationTickCumulativeLoc
    initializeObservationAfterTickState loc
  simp only [valueToWord, EVM.wordOfInt, bind, Option.bind]
  congr 2
  apply u256_inj
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner { val := 8 }
  show fromBytes'
      ((List.take 4 ↑(EVM.Word.toBytesLEWithSizeProof w) ++
          List.take 7 ↑(EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0))) ++
        List.drop (4 + 7) ↑(EVM.Word.toBytesLEWithSizeProof w)) =
    (initializeObservationAfterTickWord evm).toNat
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  rw [show 256 ^ (4 : Nat) = 2 ^ 32 by norm_num [Nat.pow_add]]
  rw [show 256 ^ (7 : Nat) = 2 ^ 56 by norm_num [Nat.pow_add]]
  rw [show 256 ^ (11 : Nat) = 2 ^ 88 by norm_num [Nat.pow_add]]
  have hlen4 : (List.take 4 (EVM.Word.toBytesLEWithSizeProof w).1).length = 4 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof w).2]
    norm_num
  have hlen11 :
      (List.take 4 (EVM.Word.toBytesLEWithSizeProof w).1 ++
          List.take 7 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0)).1).length = 11 := by
    rw [List.length_append, hlen4]
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0)).2]
    norm_num
  rw [hlen4, hlen11]
  rw [show (UInt256.ofNat 0).toNat % 2 ^ 56 = 0 by native_decide]
  rw [show (initializeObservationAfterTickWord evm).toNat =
      w.toNat % 2 ^ 32 + w.toNat / 2 ^ 88 * 2 ^ 88 by
    dsimp [initializeObservationAfterTickWord, w]
    exact ulit_toNat' _ (initializeObservationAfterTickWord_nat_lt evm)]
  ring

theorem assignStorageRef_initializeObservation_tickCumulative_zero {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? (config v)
        { contract := contract v, locals := initializeStoreWithTickAndTime I }
        evm .storage (observationsF (.intLit 0) "tickCumulative") (.int 0) =
      .ok ({ contract := contract v, locals := initializeStoreWithTickAndTime I },
        initializeObservationAfterTickState evm) := by
  apply assignStorageRef_storage_scalar_value
      (er := initializeObservationEvaledRef "tickCumulative")
      (ty := .elem (.int int56Int))
      (loc := initializeObservationTickCumulativeLoc)
  · simp [observationsF, initializeStoreWithTickAndTime, initializeStoreWithTick,
      initializeStore]
  · exact evalStorageRef_initializeObservation_withTickAndTime evm I "tickCumulative"
  · simp [contract, storageDecls, storageTypeAt?, initializeObservationEvaledRef,
      observationStructTy, int56St]
    native_decide
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      initializeObservationEvaledRef, initializeObservationTickCumulativeLoc, loc,
      initializeObservationBase_zero]
  · trivial
  · exact storageLocStore_initializeObservation_tick_zero evm

theorem initializeObservationAfterSecondsWord_nat_lt (evm : EVM.State) :
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat % 2 ^ 88 +
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat / 2 ^ 248 *
          2 ^ 248 <
      UInt256.size := by
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩
  have hlow : w.toNat % 2 ^ 88 ≤ 2 ^ 88 - 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
  have hhighLt : w.toNat / 2 ^ 248 < 2 ^ 8 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 248 * 2 ^ 8 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change w.val.val < UInt256.size
    exact w.val.isLt
  have hhigh : w.toNat / 2 ^ 248 ≤ 2 ^ 8 - 1 := Nat.le_pred_of_lt hhighLt
  have hmax : (2 ^ 88 - 1) + (2 ^ 8 - 1) * 2 ^ 248 < UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  dsimp [w] at hlow hhigh
  omega

theorem storageLocStore_initializeObservation_seconds_zero (evm : EVM.State) :
    storageLocStore evm initializeObservationSecondsPerLiquidityLoc (.int 0) =
      some (initializeObservationAfterSecondsState evm) := by
  unfold storageLocStore storageLocWriteWord initializeObservationSecondsPerLiquidityLoc
    initializeObservationAfterSecondsState loc
  simp only [valueToWord, EVM.wordOfInt, bind, Option.bind]
  congr 2
  apply u256_inj
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner { val := 8 }
  show fromBytes'
      ((List.take 11 ↑(EVM.Word.toBytesLEWithSizeProof w) ++
          List.take 20 ↑(EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0))) ++
        List.drop (11 + 20) ↑(EVM.Word.toBytesLEWithSizeProof w)) =
    (initializeObservationAfterSecondsWord evm).toNat
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  rw [show 256 ^ (11 : Nat) = 2 ^ 88 by norm_num [Nat.pow_add]]
  rw [show 256 ^ (20 : Nat) = 2 ^ 160 by norm_num [Nat.pow_add]]
  rw [show 256 ^ (31 : Nat) = 2 ^ 248 by norm_num [Nat.pow_add]]
  have hlen11 : (List.take 11 (EVM.Word.toBytesLEWithSizeProof w).1).length = 11 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof w).2]
    norm_num
  have hlen31 :
      (List.take 11 (EVM.Word.toBytesLEWithSizeProof w).1 ++
          List.take 20 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0)).1).length =
        31 := by
    rw [List.length_append, hlen11]
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0)).2]
    norm_num
  rw [hlen11, hlen31]
  rw [show (UInt256.ofNat 0).toNat % 2 ^ 160 = 0 by native_decide]
  rw [show (initializeObservationAfterSecondsWord evm).toNat =
      w.toNat % 2 ^ 88 + w.toNat / 2 ^ 248 * 2 ^ 248 by
    dsimp [initializeObservationAfterSecondsWord, w]
    exact ulit_toNat' _ (initializeObservationAfterSecondsWord_nat_lt evm)]
  ring

theorem assignStorageRef_initializeObservation_seconds_zero {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? (config v)
        { contract := contract v, locals := initializeStoreWithTickAndTime I }
        evm .storage (observationsF (.intLit 0) "secondsPerLiquidityCumulativeX128") (.int 0) =
      .ok ({ contract := contract v, locals := initializeStoreWithTickAndTime I },
        initializeObservationAfterSecondsState evm) := by
  apply assignStorageRef_storage_scalar_value
      (er := initializeObservationEvaledRef "secondsPerLiquidityCumulativeX128")
      (ty := .elem (.int uint160Int))
      (loc := initializeObservationSecondsPerLiquidityLoc)
  · simp [observationsF, initializeStoreWithTickAndTime, initializeStoreWithTick,
      initializeStore]
  · exact evalStorageRef_initializeObservation_withTickAndTime evm I
      "secondsPerLiquidityCumulativeX128"
  · simp [contract, storageDecls, storageTypeAt?, initializeObservationEvaledRef,
      observationStructTy, uint160St]
    native_decide
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      initializeObservationEvaledRef, initializeObservationSecondsPerLiquidityLoc, loc,
      initializeObservationBase_zero]
  · trivial
  · exact storageLocStore_initializeObservation_seconds_zero evm

theorem storageLocStore_initializeObservation_initialized_isSome (evm : EVM.State) :
    (storageLocStore evm initializeObservationInitializedLoc (.bool true)).isSome := by
  unfold storageLocStore storageLocWriteWord initializeObservationInitializedLoc
  simp only [valueToWord, Bool.toUInt256_true, bind, Option.bind, Option.isSome_some]

noncomputable def initializeObservationAfterInitializedState (evm : EVM.State) : EVM.State :=
  (storageLocStore evm initializeObservationInitializedLoc (.bool true)).get
    (storageLocStore_initializeObservation_initialized_isSome evm)

theorem storageLocStore_initializeObservation_initialized_true (evm : EVM.State) :
    storageLocStore evm initializeObservationInitializedLoc (.bool true) =
      some (initializeObservationAfterInitializedState evm) := by
  exact (Option.some_get (storageLocStore_initializeObservation_initialized_isSome evm)).symm

theorem storageLocStore_createdAccounts_of {evm evm' : EVM.State}
    {loc : StorageLoc} {value : Value}
    (h : storageLocStore evm loc value = some evm') :
    evm'.createdAccounts = evm.createdAccounts := by
  unfold storageLocStore at h
  cases hv : valueToWord value with
  | none => simp [hv] at h
  | some valueWord =>
      simp [hv, bind, Option.bind] at h
      cases h
      simp [storageStore_createdAccounts]

theorem storageLocStore_executionEnv_of {evm evm' : EVM.State}
    {loc : StorageLoc} {value : Value}
    (h : storageLocStore evm loc value = some evm') :
    evm'.executionEnv = evm.executionEnv := by
  unfold storageLocStore at h
  cases hv : valueToWord value with
  | none => simp [hv] at h
  | some valueWord =>
      simp [hv, bind, Option.bind] at h
      cases h
      simp [storageStore_executionEnv]

theorem assignStorageRef_initializeObservation_initialized_true {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? (config v)
        { contract := contract v, locals := initializeStoreWithTickAndTime I }
        evm .storage (observationsF (.intLit 0) "initialized") (.bool true) =
      .ok ({ contract := contract v, locals := initializeStoreWithTickAndTime I },
        initializeObservationAfterInitializedState evm) := by
  apply assignStorageRef_storage_scalar_value
      (er := initializeObservationEvaledRef "initialized")
      (ty := .elem .bool)
      (loc := initializeObservationInitializedLoc)
  · simp [observationsF, initializeStoreWithTickAndTime, initializeStoreWithTick,
      initializeStore]
  · exact evalStorageRef_initializeObservation_withTickAndTime evm I "initialized"
  · simp [contract, storageDecls, storageTypeAt?, initializeObservationEvaledRef,
      observationStructTy, boolSt]
    native_decide
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      initializeObservationEvaledRef, initializeObservationInitializedLoc,
      initializeObservationBase_zero, loc]
  · trivial
  · exact storageLocStore_initializeObservation_initialized_true evm

noncomputable def initializeObservationAfterAllState (evm : EVM.State) (I : ExecutionEnv) :
    EVM.State :=
  initializeObservationAfterInitializedState
    (initializeObservationAfterSecondsState
      (initializeObservationAfterTickState
        (initializeObservationAfterTimestampState evm I)))

theorem uniswapV3PoolInitializeSourceObservationStores {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := initializeStoreWithTickAndTime I }
      evm
      [ .assign .storage (observationsF (.intLit 0) "blockTimestamp") (.var "time"),
        .assign .storage (observationsF (.intLit 0) "tickCumulative") (.intLit 0),
        .assign .storage (observationsF (.intLit 0) "secondsPerLiquidityCumulativeX128")
          (.intLit 0),
        .assign .storage (observationsF (.intLit 0) "initialized") (.boolLit true) ]
      (.ok { contract := contract v, locals := initializeStoreWithTickAndTime I }
        (initializeObservationAfterAllState evm I)) := by
  unfold initializeObservationAfterAllState
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_initializeTimeVar evm I)
      (assignStorageRef_initializeObservation_blockTimestamp evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (assignStorageRef_initializeObservation_tickCumulative_zero
        (initializeObservationAfterTimestampState evm I) I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (assignStorageRef_initializeObservation_seconds_zero
        (initializeObservationAfterTickState (initializeObservationAfterTimestampState evm I)) I)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (assignStorageRef_initializeObservation_initialized_true
        (initializeObservationAfterSecondsState
          (initializeObservationAfterTickState (initializeObservationAfterTimestampState evm I))) I))
    ExecBlock.nil

theorem initializeObservationAfterAllState_createdAccounts
    (evm : EVM.State) (I : ExecutionEnv) :
    (initializeObservationAfterAllState evm I).createdAccounts = evm.createdAccounts := by
  unfold initializeObservationAfterAllState
  rw [storageLocStore_createdAccounts_of
    (storageLocStore_initializeObservation_initialized_true
      (initializeObservationAfterSecondsState
        (initializeObservationAfterTickState (initializeObservationAfterTimestampState evm I))))]
  simp [initializeObservationAfterSecondsState, initializeObservationAfterTickState,
    initializeObservationAfterTimestampState, storageStore_createdAccounts]

theorem initializeObservationAfterAllState_executionEnv
    (evm : EVM.State) (I : ExecutionEnv) :
    (initializeObservationAfterAllState evm I).executionEnv = evm.executionEnv := by
  unfold initializeObservationAfterAllState
  rw [storageLocStore_executionEnv_of
    (storageLocStore_initializeObservation_initialized_true
      (initializeObservationAfterSecondsState
        (initializeObservationAfterTickState (initializeObservationAfterTimestampState evm I))))]
  simp [initializeObservationAfterSecondsState, initializeObservationAfterTickState,
    initializeObservationAfterTimestampState, storageStore_executionEnv]

theorem uniswapV3PoolInitializeSourceObservationTail {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) (hEnv : evm.executionEnv = I) :
    ExecBlock (config v) { contract := contract v, locals := initializeStoreWithTick I }
      evm
      [ .letDecl "time" (some uint32) (modE (.env .timestamp) uint32Modulus),
        .assign .storage (observationsF (.intLit 0) "blockTimestamp") (.var "time"),
        .assign .storage (observationsF (.intLit 0) "tickCumulative") (.intLit 0),
        .assign .storage (observationsF (.intLit 0) "secondsPerLiquidityCumulativeX128")
          (.intLit 0),
        .assign .storage (observationsF (.intLit 0) "initialized") (.boolLit true) ]
      (.ok { contract := contract v, locals := initializeStoreWithTickAndTime I }
        (initializeObservationAfterAllState evm I)) := by
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_initializeTime_withTick evm I hEnv)) ?_
  exact uniswapV3PoolInitializeSourceObservationStores evm I

abbrev initializeSlot0SqrtPriceX96Loc : StorageLoc :=
  loc ⟨0⟩ ⟨0, by decide⟩ ⟨20, by decide⟩ (by decide) (.int uint160Int)

abbrev initializeSlot0TickLoc : StorageLoc :=
  loc ⟨0⟩ ⟨20, by decide⟩ ⟨3, by decide⟩ (by decide) (.int int24Int)

abbrev initializeSlot0ObservationIndexLoc : StorageLoc :=
  loc ⟨0⟩ ⟨23, by decide⟩ ⟨2, by decide⟩ (by decide) (.int uint16Int)

abbrev initializeSlot0ObservationCardinalityLoc : StorageLoc :=
  loc ⟨0⟩ ⟨25, by decide⟩ ⟨2, by decide⟩ (by decide) (.int uint16Int)

abbrev initializeSlot0ObservationCardinalityNextLoc : StorageLoc :=
  loc ⟨0⟩ ⟨27, by decide⟩ ⟨2, by decide⟩ (by decide) (.int uint16Int)

abbrev initializeSlot0FeeProtocolLoc : StorageLoc :=
  loc ⟨0⟩ ⟨29, by decide⟩ ⟨1, by decide⟩ (by decide) (.int uint8Int)

abbrev initializeSlot0UnlockedLoc : StorageLoc :=
  loc ⟨0⟩ ⟨30, by decide⟩ ⟨1, by decide⟩ (by decide) .bool

private theorem storageLocStore_int_value_isSome (evm : EVM.State) (loc : StorageLoc)
    (n : Int) :
    (storageLocStore evm loc (.int n)).isSome := by
  obtain ⟨evm', h⟩ := storageLocStore_int_some evm loc n
  rw [h]
  rfl

theorem storageLocStore_initializeSlot0_sqrtPriceX96_isSome
    (evm : EVM.State) (I : ExecutionEnv) :
    (storageLocStore evm initializeSlot0SqrtPriceX96Loc (initializeArgValue I)).isSome := by
  rw [show initializeArgValue I = .int (Int.ofNat (initializeArgWord I).toNat) by rfl]
  exact storageLocStore_int_value_isSome evm initializeSlot0SqrtPriceX96Loc _

noncomputable def initializeSlot0AfterSqrtPriceX96State
    (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  (storageLocStore evm initializeSlot0SqrtPriceX96Loc (initializeArgValue I)).get
    (storageLocStore_initializeSlot0_sqrtPriceX96_isSome evm I)

theorem storageLocStore_initializeSlot0_sqrtPriceX96
    (evm : EVM.State) (I : ExecutionEnv) :
    storageLocStore evm initializeSlot0SqrtPriceX96Loc (initializeArgValue I) =
      some (initializeSlot0AfterSqrtPriceX96State evm I) := by
  exact (Option.some_get (storageLocStore_initializeSlot0_sqrtPriceX96_isSome evm I)).symm

theorem initializeSlot0AfterSqrtPriceX96State_createdAccounts
    (evm : EVM.State) (I : ExecutionEnv) :
    (initializeSlot0AfterSqrtPriceX96State evm I).createdAccounts =
      evm.createdAccounts :=
  storageLocStore_createdAccounts_of (storageLocStore_initializeSlot0_sqrtPriceX96 evm I)

theorem storageLocStore_initializeSlot0_tick_isSome
    (evm : EVM.State) (I : ExecutionEnv) :
    (storageLocStore evm initializeSlot0TickLoc (initializeTickValue I)).isSome := by
  rw [show initializeTickValue I = .int (Int.ofNat (getTickEstimatedWord I).toNat) by rfl]
  exact storageLocStore_int_value_isSome evm initializeSlot0TickLoc _

noncomputable def initializeSlot0AfterTickState
    (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  (storageLocStore evm initializeSlot0TickLoc (initializeTickValue I)).get
    (storageLocStore_initializeSlot0_tick_isSome evm I)

theorem storageLocStore_initializeSlot0_tick (evm : EVM.State) (I : ExecutionEnv) :
    storageLocStore evm initializeSlot0TickLoc (initializeTickValue I) =
      some (initializeSlot0AfterTickState evm I) := by
  exact (Option.some_get (storageLocStore_initializeSlot0_tick_isSome evm I)).symm

theorem initializeSlot0AfterTickState_createdAccounts
    (evm : EVM.State) (I : ExecutionEnv) :
    (initializeSlot0AfterTickState evm I).createdAccounts = evm.createdAccounts :=
  storageLocStore_createdAccounts_of (storageLocStore_initializeSlot0_tick evm I)

theorem storageLocStore_initializeSlot0_observationIndex_isSome (evm : EVM.State) :
    (storageLocStore evm initializeSlot0ObservationIndexLoc (.int 0)).isSome :=
  storageLocStore_int_value_isSome evm initializeSlot0ObservationIndexLoc 0

noncomputable def initializeSlot0AfterObservationIndexState
    (evm : EVM.State) : EVM.State :=
  (storageLocStore evm initializeSlot0ObservationIndexLoc (.int 0)).get
    (storageLocStore_initializeSlot0_observationIndex_isSome evm)

theorem storageLocStore_initializeSlot0_observationIndex (evm : EVM.State) :
    storageLocStore evm initializeSlot0ObservationIndexLoc (.int 0) =
      some (initializeSlot0AfterObservationIndexState evm) := by
  exact (Option.some_get (storageLocStore_initializeSlot0_observationIndex_isSome evm)).symm

theorem initializeSlot0AfterObservationIndexState_createdAccounts
    (evm : EVM.State) :
    (initializeSlot0AfterObservationIndexState evm).createdAccounts = evm.createdAccounts :=
  storageLocStore_createdAccounts_of (storageLocStore_initializeSlot0_observationIndex evm)

theorem storageLocStore_initializeSlot0_observationCardinality_isSome (evm : EVM.State) :
    (storageLocStore evm initializeSlot0ObservationCardinalityLoc (.int 1)).isSome :=
  storageLocStore_int_value_isSome evm initializeSlot0ObservationCardinalityLoc 1

noncomputable def initializeSlot0AfterObservationCardinalityState
    (evm : EVM.State) : EVM.State :=
  (storageLocStore evm initializeSlot0ObservationCardinalityLoc (.int 1)).get
    (storageLocStore_initializeSlot0_observationCardinality_isSome evm)

theorem storageLocStore_initializeSlot0_observationCardinality (evm : EVM.State) :
    storageLocStore evm initializeSlot0ObservationCardinalityLoc (.int 1) =
      some (initializeSlot0AfterObservationCardinalityState evm) := by
  exact (Option.some_get
    (storageLocStore_initializeSlot0_observationCardinality_isSome evm)).symm

theorem initializeSlot0AfterObservationCardinalityState_createdAccounts
    (evm : EVM.State) :
    (initializeSlot0AfterObservationCardinalityState evm).createdAccounts =
      evm.createdAccounts :=
  storageLocStore_createdAccounts_of
    (storageLocStore_initializeSlot0_observationCardinality evm)

theorem storageLocStore_initializeSlot0_observationCardinalityNext_isSome (evm : EVM.State) :
    (storageLocStore evm initializeSlot0ObservationCardinalityNextLoc (.int 1)).isSome :=
  storageLocStore_int_value_isSome evm initializeSlot0ObservationCardinalityNextLoc 1

noncomputable def initializeSlot0AfterObservationCardinalityNextState
    (evm : EVM.State) : EVM.State :=
  (storageLocStore evm initializeSlot0ObservationCardinalityNextLoc (.int 1)).get
    (storageLocStore_initializeSlot0_observationCardinalityNext_isSome evm)

theorem storageLocStore_initializeSlot0_observationCardinalityNext (evm : EVM.State) :
    storageLocStore evm initializeSlot0ObservationCardinalityNextLoc (.int 1) =
      some (initializeSlot0AfterObservationCardinalityNextState evm) := by
  exact (Option.some_get
    (storageLocStore_initializeSlot0_observationCardinalityNext_isSome evm)).symm

theorem initializeSlot0AfterObservationCardinalityNextState_createdAccounts
    (evm : EVM.State) :
    (initializeSlot0AfterObservationCardinalityNextState evm).createdAccounts =
      evm.createdAccounts :=
  storageLocStore_createdAccounts_of
    (storageLocStore_initializeSlot0_observationCardinalityNext evm)

theorem storageLocStore_initializeSlot0_feeProtocol_isSome (evm : EVM.State) :
    (storageLocStore evm initializeSlot0FeeProtocolLoc (.int 0)).isSome :=
  storageLocStore_int_value_isSome evm initializeSlot0FeeProtocolLoc 0

noncomputable def initializeSlot0AfterFeeProtocolState (evm : EVM.State) : EVM.State :=
  (storageLocStore evm initializeSlot0FeeProtocolLoc (.int 0)).get
    (storageLocStore_initializeSlot0_feeProtocol_isSome evm)

theorem storageLocStore_initializeSlot0_feeProtocol (evm : EVM.State) :
    storageLocStore evm initializeSlot0FeeProtocolLoc (.int 0) =
      some (initializeSlot0AfterFeeProtocolState evm) := by
  exact (Option.some_get (storageLocStore_initializeSlot0_feeProtocol_isSome evm)).symm

theorem initializeSlot0AfterFeeProtocolState_createdAccounts (evm : EVM.State) :
    (initializeSlot0AfterFeeProtocolState evm).createdAccounts = evm.createdAccounts :=
  storageLocStore_createdAccounts_of (storageLocStore_initializeSlot0_feeProtocol evm)

theorem storageLocStore_initializeSlot0_unlocked_isSome (evm : EVM.State) :
    (storageLocStore evm initializeSlot0UnlockedLoc (.bool true)).isSome := by
  unfold storageLocStore storageLocWriteWord initializeSlot0UnlockedLoc
  simp only [valueToWord, Bool.toUInt256_true, bind, Option.bind, Option.isSome_some]

noncomputable def initializeSlot0AfterUnlockedState (evm : EVM.State) : EVM.State :=
  (storageLocStore evm initializeSlot0UnlockedLoc (.bool true)).get
    (storageLocStore_initializeSlot0_unlocked_isSome evm)

theorem storageLocStore_initializeSlot0_unlocked_true (evm : EVM.State) :
    storageLocStore evm initializeSlot0UnlockedLoc (.bool true) =
      some (initializeSlot0AfterUnlockedState evm) := by
  exact (Option.some_get (storageLocStore_initializeSlot0_unlocked_isSome evm)).symm

theorem initializeSlot0AfterUnlockedState_createdAccounts (evm : EVM.State) :
    (initializeSlot0AfterUnlockedState evm).createdAccounts = evm.createdAccounts :=
  storageLocStore_createdAccounts_of (storageLocStore_initializeSlot0_unlocked_true evm)

noncomputable def initializeSlot0AfterAllState (evm : EVM.State) (I : ExecutionEnv) :
    EVM.State :=
  initializeSlot0AfterUnlockedState
    (initializeSlot0AfterFeeProtocolState
      (initializeSlot0AfterObservationCardinalityNextState
        (initializeSlot0AfterObservationCardinalityState
          (initializeSlot0AfterObservationIndexState
            (initializeSlot0AfterTickState
              (initializeSlot0AfterSqrtPriceX96State evm I) I)))))

theorem initializeSlot0AfterAllState_createdAccounts
    (evm : EVM.State) (I : ExecutionEnv) :
    (initializeSlot0AfterAllState evm I).createdAccounts = evm.createdAccounts := by
  unfold initializeSlot0AfterAllState
  rw [initializeSlot0AfterUnlockedState_createdAccounts]
  rw [initializeSlot0AfterFeeProtocolState_createdAccounts]
  rw [initializeSlot0AfterObservationCardinalityNextState_createdAccounts]
  rw [initializeSlot0AfterObservationCardinalityState_createdAccounts]
  rw [initializeSlot0AfterObservationIndexState_createdAccounts]
  rw [initializeSlot0AfterTickState_createdAccounts]
  exact initializeSlot0AfterSqrtPriceX96State_createdAccounts evm I

theorem initializeSlot0AfterAllState_executionEnv
    (evm : EVM.State) (I : ExecutionEnv) :
    (initializeSlot0AfterAllState evm I).executionEnv = evm.executionEnv := by
  unfold initializeSlot0AfterAllState
  rw [storageLocStore_executionEnv_of (storageLocStore_initializeSlot0_unlocked_true _)]
  rw [storageLocStore_executionEnv_of (storageLocStore_initializeSlot0_feeProtocol _)]
  rw [storageLocStore_executionEnv_of
    (storageLocStore_initializeSlot0_observationCardinalityNext _)]
  rw [storageLocStore_executionEnv_of
    (storageLocStore_initializeSlot0_observationCardinality _)]
  rw [storageLocStore_executionEnv_of
    (storageLocStore_initializeSlot0_observationIndex _)]
  rw [storageLocStore_executionEnv_of (storageLocStore_initializeSlot0_tick _ I)]
  exact storageLocStore_executionEnv_of (storageLocStore_initializeSlot0_sqrtPriceX96 evm I)

theorem initializeStoreWithTickAndTime_sqrtPriceX96 (I : ExecutionEnv) :
    (initializeStoreWithTickAndTime I).get? "sqrtPriceX96" =
      some (initializeArgValue I) := by
  rw [initializeStoreWithTickAndTime]
  rw [store_get_ne (initializeStoreWithTick I) (initializeTimeValue I) (by decide)]
  rw [initializeStoreWithTick]
  rw [store_get_ne (initializeStore I) (initializeTickValue I) (by decide)]
  exact store_get_self (∅ : Store) "sqrtPriceX96" (initializeArgValue I)

theorem initializeStoreWithTickAndTime_tick (I : ExecutionEnv) :
    (initializeStoreWithTickAndTime I).get? "tick" = some (initializeTickValue I) := by
  rw [initializeStoreWithTickAndTime]
  rw [store_get_ne (initializeStoreWithTick I) (initializeTimeValue I) (by decide)]
  rw [initializeStoreWithTick]
  exact store_get_self (initializeStore I) "tick" (initializeTickValue I)

theorem evalExpr_initializeSqrtPriceVar_withTickAndTime {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := initializeStoreWithTickAndTime I }
      evm (.var "sqrtPriceX96") = .ok (initializeArgValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [initializeStoreWithTickAndTime_sqrtPriceX96]

theorem evalExpr_initializeTickVar_withTickAndTime {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := initializeStoreWithTickAndTime I }
      evm (.var "tick") = .ok (initializeTickValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [initializeStoreWithTickAndTime_tick]

theorem assignStorageRef_initializeSlot0_sqrtPriceX96 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? (config v)
        { contract := contract v, locals := initializeStoreWithTickAndTime I }
        evm .storage (slot0F "sqrtPriceX96") (initializeArgValue I) =
      .ok ({ contract := contract v, locals := initializeStoreWithTickAndTime I },
        initializeSlot0AfterSqrtPriceX96State evm I) := by
  apply assignStorageRef_storage_scalar_value
      (er := { base := "slot0", steps := [.field "sqrtPriceX96"] })
      (ty := .elem (.int uint160Int))
      (loc := initializeSlot0SqrtPriceX96Loc)
  · simp [slot0F, initializeStoreWithTickAndTime, initializeStoreWithTick, initializeStore]
  · simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind]
  · simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy, uint160St]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      initializeSlot0SqrtPriceX96Loc, loc]
  · trivial
  · exact storageLocStore_initializeSlot0_sqrtPriceX96 evm I

theorem assignStorageRef_initializeSlot0_tick {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? (config v)
        { contract := contract v, locals := initializeStoreWithTickAndTime I }
        evm .storage (slot0F "tick") (initializeTickValue I) =
      .ok ({ contract := contract v, locals := initializeStoreWithTickAndTime I },
        initializeSlot0AfterTickState evm I) := by
  apply assignStorageRef_storage_scalar_value
      (er := { base := "slot0", steps := [.field "tick"] })
      (ty := .elem (.int int24Int))
      (loc := initializeSlot0TickLoc)
  · simp [slot0F, initializeStoreWithTickAndTime, initializeStoreWithTick, initializeStore]
  · simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind]
  · simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy, int24St]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      initializeSlot0TickLoc, loc]
  · trivial
  · exact storageLocStore_initializeSlot0_tick evm I

theorem assignStorageRef_initializeSlot0_observationIndex {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? (config v)
        { contract := contract v, locals := initializeStoreWithTickAndTime I }
        evm .storage (slot0F "observationIndex") (.int 0) =
      .ok ({ contract := contract v, locals := initializeStoreWithTickAndTime I },
        initializeSlot0AfterObservationIndexState evm) := by
  apply assignStorageRef_storage_scalar_value
      (er := { base := "slot0", steps := [.field "observationIndex"] })
      (ty := .elem (.int uint16Int))
      (loc := initializeSlot0ObservationIndexLoc)
  · simp [slot0F, initializeStoreWithTickAndTime, initializeStoreWithTick, initializeStore]
  · simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind]
  · simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy, uint16St]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      initializeSlot0ObservationIndexLoc, loc]
  · trivial
  · exact storageLocStore_initializeSlot0_observationIndex evm

theorem assignStorageRef_initializeSlot0_observationCardinality {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? (config v)
        { contract := contract v, locals := initializeStoreWithTickAndTime I }
        evm .storage (slot0F "observationCardinality") (.int 1) =
      .ok ({ contract := contract v, locals := initializeStoreWithTickAndTime I },
        initializeSlot0AfterObservationCardinalityState evm) := by
  apply assignStorageRef_storage_scalar_value
      (er := { base := "slot0", steps := [.field "observationCardinality"] })
      (ty := .elem (.int uint16Int))
      (loc := initializeSlot0ObservationCardinalityLoc)
  · simp [slot0F, initializeStoreWithTickAndTime, initializeStoreWithTick, initializeStore]
  · simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind]
  · simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy, uint16St]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      initializeSlot0ObservationCardinalityLoc, loc]
  · trivial
  · exact storageLocStore_initializeSlot0_observationCardinality evm

theorem assignStorageRef_initializeSlot0_observationCardinalityNext {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? (config v)
        { contract := contract v, locals := initializeStoreWithTickAndTime I }
        evm .storage (slot0F "observationCardinalityNext") (.int 1) =
      .ok ({ contract := contract v, locals := initializeStoreWithTickAndTime I },
        initializeSlot0AfterObservationCardinalityNextState evm) := by
  apply assignStorageRef_storage_scalar_value
      (er := { base := "slot0", steps := [.field "observationCardinalityNext"] })
      (ty := .elem (.int uint16Int))
      (loc := initializeSlot0ObservationCardinalityNextLoc)
  · simp [slot0F, initializeStoreWithTickAndTime, initializeStoreWithTick, initializeStore]
  · simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind]
  · simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy, uint16St]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      initializeSlot0ObservationCardinalityNextLoc, loc]
  · trivial
  · exact storageLocStore_initializeSlot0_observationCardinalityNext evm

theorem assignStorageRef_initializeSlot0_feeProtocol {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? (config v)
        { contract := contract v, locals := initializeStoreWithTickAndTime I }
        evm .storage (slot0F "feeProtocol") (.int 0) =
      .ok ({ contract := contract v, locals := initializeStoreWithTickAndTime I },
        initializeSlot0AfterFeeProtocolState evm) := by
  apply assignStorageRef_storage_scalar_value
      (er := { base := "slot0", steps := [.field "feeProtocol"] })
      (ty := .elem (.int uint8Int))
      (loc := initializeSlot0FeeProtocolLoc)
  · simp [slot0F, initializeStoreWithTickAndTime, initializeStoreWithTick, initializeStore]
  · simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind]
  · simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy, uint8St]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      initializeSlot0FeeProtocolLoc, loc]
  · trivial
  · exact storageLocStore_initializeSlot0_feeProtocol evm

theorem assignStorageRef_initializeSlot0_unlocked {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? (config v)
        { contract := contract v, locals := initializeStoreWithTickAndTime I }
        evm .storage (slot0F "unlocked") (.bool true) =
      .ok ({ contract := contract v, locals := initializeStoreWithTickAndTime I },
        initializeSlot0AfterUnlockedState evm) := by
  apply assignStorageRef_storage_scalar_value
      (er := { base := "slot0", steps := [.field "unlocked"] })
      (ty := .elem .bool)
      (loc := initializeSlot0UnlockedLoc)
  · simp [slot0F, initializeStoreWithTickAndTime, initializeStoreWithTick, initializeStore]
  · simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind]
  · simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy, boolSt]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      initializeSlot0UnlockedLoc, loc]
  · trivial
  · exact storageLocStore_initializeSlot0_unlocked_true evm

theorem uniswapV3PoolInitializeSourceSlot0Stores {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := initializeStoreWithTickAndTime I }
      evm
      [ .assign .storage (slot0F "sqrtPriceX96") (.var "sqrtPriceX96"),
        .assign .storage (slot0F "tick") (.var "tick"),
        .assign .storage (slot0F "observationIndex") (.intLit 0),
        .assign .storage (slot0F "observationCardinality") (.intLit 1),
        .assign .storage (slot0F "observationCardinalityNext") (.intLit 1),
        .assign .storage (slot0F "feeProtocol") (.intLit 0),
        .assign .storage (slot0F "unlocked") (.boolLit true) ]
      (.ok { contract := contract v, locals := initializeStoreWithTickAndTime I }
        (initializeSlot0AfterAllState evm I)) := by
  unfold initializeSlot0AfterAllState
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_initializeSqrtPriceVar_withTickAndTime evm I)
      (assignStorageRef_initializeSlot0_sqrtPriceX96 evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_initializeTickVar_withTickAndTime
      (initializeSlot0AfterSqrtPriceX96State evm I) I)
      (assignStorageRef_initializeSlot0_tick
        (initializeSlot0AfterSqrtPriceX96State evm I) I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (assignStorageRef_initializeSlot0_observationIndex
        (initializeSlot0AfterTickState
          (initializeSlot0AfterSqrtPriceX96State evm I) I) I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (assignStorageRef_initializeSlot0_observationCardinality
        (initializeSlot0AfterObservationIndexState
          (initializeSlot0AfterTickState
            (initializeSlot0AfterSqrtPriceX96State evm I) I)) I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (assignStorageRef_initializeSlot0_observationCardinalityNext
        (initializeSlot0AfterObservationCardinalityState
          (initializeSlot0AfterObservationIndexState
            (initializeSlot0AfterTickState
              (initializeSlot0AfterSqrtPriceX96State evm I) I))) I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (assignStorageRef_initializeSlot0_feeProtocol
        (initializeSlot0AfterObservationCardinalityNextState
          (initializeSlot0AfterObservationCardinalityState
            (initializeSlot0AfterObservationIndexState
              (initializeSlot0AfterTickState
                (initializeSlot0AfterSqrtPriceX96State evm I) I)))) I)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (assignStorageRef_initializeSlot0_unlocked
        (initializeSlot0AfterFeeProtocolState
          (initializeSlot0AfterObservationCardinalityNextState
            (initializeSlot0AfterObservationCardinalityState
              (initializeSlot0AfterObservationIndexState
                (initializeSlot0AfterTickState
                  (initializeSlot0AfterSqrtPriceX96State evm I) I))))) I))
    ExecBlock.nil

noncomputable def initializeSourceAfterStorageTailState
    (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  initializeSlot0AfterAllState (initializeObservationAfterAllState evm I) I

theorem initializeSourceAfterStorageTailState_createdAccounts
    (evm : EVM.State) (I : ExecutionEnv) :
    (initializeSourceAfterStorageTailState evm I).createdAccounts = evm.createdAccounts := by
  unfold initializeSourceAfterStorageTailState
  rw [initializeSlot0AfterAllState_createdAccounts]
  exact initializeObservationAfterAllState_createdAccounts evm I

theorem initializeSourceAfterStorageTailState_executionEnv
    (evm : EVM.State) (I : ExecutionEnv) :
    (initializeSourceAfterStorageTailState evm I).executionEnv = evm.executionEnv := by
  unfold initializeSourceAfterStorageTailState
  rw [initializeSlot0AfterAllState_executionEnv]
  exact initializeObservationAfterAllState_executionEnv evm I

theorem uniswapV3PoolInitializeSourceStorageTail {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) (hEnv : evm.executionEnv = I) :
    ExecBlock (config v) { contract := contract v, locals := initializeStoreWithTick I }
      evm
      [ .letDecl "time" (some uint32) (modE (.env .timestamp) uint32Modulus),
        .assign .storage (observationsF (.intLit 0) "blockTimestamp") (.var "time"),
        .assign .storage (observationsF (.intLit 0) "tickCumulative") (.intLit 0),
        .assign .storage (observationsF (.intLit 0) "secondsPerLiquidityCumulativeX128")
          (.intLit 0),
        .assign .storage (observationsF (.intLit 0) "initialized") (.boolLit true),
        .assign .storage (slot0F "sqrtPriceX96") (.var "sqrtPriceX96"),
        .assign .storage (slot0F "tick") (.var "tick"),
        .assign .storage (slot0F "observationIndex") (.intLit 0),
        .assign .storage (slot0F "observationCardinality") (.intLit 1),
        .assign .storage (slot0F "observationCardinalityNext") (.intLit 1),
        .assign .storage (slot0F "feeProtocol") (.intLit 0),
        .assign .storage (slot0F "unlocked") (.boolLit true) ]
      (.ok { contract := contract v, locals := initializeStoreWithTickAndTime I }
        (initializeSourceAfterStorageTailState evm I)) := by
  have hobs := uniswapV3PoolInitializeSourceObservationTail (v := v) evm I hEnv
  have hslot0 := uniswapV3PoolInitializeSourceSlot0Stores (v := v)
    (initializeObservationAfterAllState evm I) I
  simpa [initializeSourceAfterStorageTailState] using execBlock_append hobs hslot0

theorem uniswapV3PoolInitializeSourceSuccessBodyFromGetTick {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hzero : slot0SqrtPriceX96Word σ I = ⟨0⟩)
    (hgetTick :
      ExecStmt (config v) { contract := contract v, locals := initializeStore I }
        (initState cA gh bl σ σ₀ g A I)
        (.internalCall "getTickAtSqrtRatio" [.var "sqrtPriceX96"] "tick")
        (.ok { contract := contract v, locals := initializeStoreWithTick I }
          (initState cA gh bl σ σ₀ g A I))) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (initializeStore I)
      initializeTransition.body
      (.returned { contract := contract v, locals := initializeStoreWithTickAndTime I }
        (initializeSourceAfterStorageTailState (initState cA gh bl σ σ₀ g A I) I)
        none) := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (initializeStore I)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (eqE (.storage (slot0F "sqrtPriceX96")) (.intLit 0)),
        .internalCall "getTickAtSqrtRatio" [.var "sqrtPriceX96"] "tick",
        .letDecl "time" (some uint32) (modE (.env .timestamp) uint32Modulus),
        .assign .storage (observationsF (.intLit 0) "blockTimestamp") (.var "time"),
        .assign .storage (observationsF (.intLit 0) "tickCumulative") (.intLit 0),
        .assign .storage (observationsF (.intLit 0) "secondsPerLiquidityCumulativeX128")
          (.intLit 0),
        .assign .storage (observationsF (.intLit 0) "initialized") (.boolLit true),
        .assign .storage (slot0F "sqrtPriceX96") (.var "sqrtPriceX96"),
        .assign .storage (slot0F "tick") (.var "tick"),
        .assign .storage (slot0F "observationIndex") (.intLit 0),
        .assign .storage (slot0F "observationCardinality") (.intLit 1),
        .assign .storage (slot0F "observationCardinalityNext") (.intLit 1),
        .assign .storage (slot0F "feeProtocol") (.intLit 0),
        .assign .storage (slot0F "unlocked") (.boolLit true) ]
      (.returned { contract := contract v, locals := initializeStoreWithTickAndTime I }
        (initializeSourceAfterStorageTailState (initState cA gh bl σ σ₀ g A I) I)
        none)
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp [initState, hwv]))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (uniswapV3PoolInitializeEvalSqrtPriceX96EqZeroTrue (v := v) hzero)) ?_
  refine ExecBlock.consNormal hgetTick ?_
  exact uniswapV3PoolInitializeSourceStorageTail
    (initState cA gh bl σ σ₀ g A I) I (by simp [initState])

theorem uniswapV3PoolInitializeSourceGetTickStatementSuccess {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} {calleeSolm : Frame}
    (hbody :
      ExecFuncBody (config v) { contract := contract v, locals := initializeStore I }
        (initState cA gh bl σ σ₀ g A I) getTickAtSqrtRatioFunction.body
        (.returned calleeSolm (initState cA gh bl σ σ₀ g A I)
          (some [initializeTickValue I]))) :
    ExecStmt (config v) { contract := contract v, locals := initializeStore I }
      (initState cA gh bl σ σ₀ g A I)
      (.internalCall "getTickAtSqrtRatio" [.var "sqrtPriceX96"] "tick")
      (.ok { contract := contract v, locals := initializeStoreWithTick I }
        (initState cA gh bl σ σ₀ g A I)) := by
  have hstmt := internalCallFunctionReturn
    (cfg := config v)
    (caller := { contract := contract v, locals := initializeStore I })
    (evm := initState cA gh bl σ σ₀ g A I)
    (calleeEvm := initState cA gh bl σ σ₀ g A I)
    (name := "getTickAtSqrtRatio") (retVar := "tick")
    (args := [.var "sqrtPriceX96"]) (argVals := [initializeArgValue I])
    (callee := getTickAtSqrtRatioFunction) (locals := initializeStore I)
    (calleeSolm := calleeSolm) (value := some [initializeTickValue I])
    (by
      simp [evalExprs?, uniswapV3PoolInitializeEvalSqrtPriceVar, EvalResult.bind, bind, pure])
    (by
      simp [lookupCallable?, lookupFunction?, contract, functions, getSqrtRatioAtTickFunction,
        getTickAtSqrtRatioFunction])
    (by rfl)
    hbody
  simpa [resumeAfterInternalCall, collapseReturns, initializeStoreWithTick] using hstmt

theorem uniswapV3PoolInitializeSourceSuccessBodyOfGetTickFunc {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} {calleeSolm : Frame}
    (hwv : I.weiValue = ⟨0⟩)
    (hzero : slot0SqrtPriceX96Word σ I = ⟨0⟩)
    (hgetTickBody :
      ExecFuncBody (config v) { contract := contract v, locals := initializeStore I }
        (initState cA gh bl σ σ₀ g A I) getTickAtSqrtRatioFunction.body
        (.returned calleeSolm (initState cA gh bl σ σ₀ g A I)
          (some [initializeTickValue I]))) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (initializeStore I)
      initializeTransition.body
      (.returned { contract := contract v, locals := initializeStoreWithTickAndTime I }
        (initializeSourceAfterStorageTailState (initState cA gh bl σ σ₀ g A I) I)
        none) := by
  exact uniswapV3PoolInitializeSourceSuccessBodyFromGetTick (v := v) hwv hzero
    (uniswapV3PoolInitializeSourceGetTickStatementSuccess (v := v) hgetTickBody)

private theorem initializeObservationLow32_merge (low old : UInt256)
    (hlow : low.toNat < 2 ^ 32) :
    UInt256.land (⟨4294967295⟩ : UInt256)
        (UInt256.lor low (UInt256.land (UInt256.lnot (⟨4294967295⟩ : UInt256)) old)) =
      low := by
  apply u256_inj
  have hmask32 : (⟨4294967295⟩ : UInt256).toNat = 2 ^ 32 - 1 := by native_decide
  have hclearMask : UInt256.lnot (⟨4294967295⟩ : UInt256) =
      UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 32) := by
    native_decide
  have hhigh :
      (UInt256.land (UInt256.lnot (⟨4294967295⟩ : UInt256)) old).toNat =
        old.toNat / 2 ^ 32 * 2 ^ 32 := by
    rw [hclearMask]
    exact u256_land_high_mask_toNat old 32 (by norm_num)
  have hq : old.toNat / 2 ^ 32 < 2 ^ 224 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 32 * 2 ^ 224 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change old.val.val < 2 ^ 256
    simp [UInt256.size]
  have hlorLt :
      Nat.lor low.toNat
          ((UInt256.land (UInt256.lnot (⟨4294967295⟩ : UInt256)) old).toNat) <
        UInt256.size := by
    rw [hhigh]
    rw [nat_lor_shift_add low.toNat (old.toNat / 2 ^ 32) 32 hlow]
    have hqle : old.toNat / 2 ^ 32 ≤ 2 ^ 224 - 1 := Nat.le_pred_of_lt hq
    have hprod : (old.toNat / 2 ^ 32) * 2 ^ 32 ≤ (2 ^ 224 - 1) * 2 ^ 32 := by
      exact Nat.mul_le_mul_right _ hqle
    norm_num [UInt256.size, Nat.pow_add] at hprod ⊢
    omega
  rw [u256_land_toNat]
  rw [hmask32]
  rw [nat_land_comm]
  rw [nat_land_mask_eq_mod]
  rw [Nat.mod_eq_of_lt (by
    exact lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 32)) (by norm_num [UInt256.size]))]
  rw [u256_lor_toNat]
  rw [Nat.mod_eq_of_lt hlorLt]
  rw [hhigh]
  rw [nat_lor_shift_add low.toNat (old.toNat / 2 ^ 32) 32 hlow]
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt hlow

theorem initializeObservationSstoreWord_eq_timestamp (σ : AccountMap) (ee : ExecutionEnv) :
    initializeObservationSstoreWord σ ee =
      UInt256.lor (UInt256.shiftLeft ⟨1⟩ ⟨248⟩) (initializeObservationTimestampWord ee) := by
  unfold initializeObservationSstoreWord
  rw [initializeObservationLow32_merge]
  unfold initializeObservationTimestampWord
  rw [u256_land_toNat]
  have hmask32 : (⟨4294967295⟩ : UInt256).toNat = 2 ^ 32 - 1 := by native_decide
  rw [hmask32, nat_land_comm, nat_land_mask_eq_mod]
  rw [Nat.mod_eq_of_lt (by
    exact lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 32)) (by norm_num [UInt256.size]))]
  exact Nat.mod_lt _ (by norm_num)

theorem initializeObservationAccountMapEquiv {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner σ_evm ⟨8⟩ (initializeObservationSstoreWord σ_evm I))
      (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner ⟨8⟩
        (UInt256.lor (UInt256.shiftLeft ⟨1⟩ ⟨248⟩)
          (initializeObservationTimestampWord I))).accountMap := by
  rw [initializeObservationSstoreWord_eq_timestamp]
  simpa [storageStore_accountMap, initState] using
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨8⟩
      (UInt256.lor (UInt256.shiftLeft ⟨1⟩ ⟨248⟩) (initializeObservationTimestampWord I))
      hAccounts

end Benchmarks.UniswapV3Pool

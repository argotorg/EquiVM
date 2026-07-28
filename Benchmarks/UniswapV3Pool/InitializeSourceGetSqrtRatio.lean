import Benchmarks.UniswapV3Pool.InitializeSourceGetTickPostLog

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

theorem getTickStoreForSqrtRatioAtTickHiCall_tick (I : ExecutionEnv) :
    (getTickStoreForSqrtRatioAtTickHiCall I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  rw [getTickStoreForSqrtRatioAtTickHiCall, store_get_self]

theorem evalExpr_getSqrtRatio_tickVar_forTickHi {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
        { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I }
        evm (.var "tick") = .ok (getTickSourceTickHiValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreForSqrtRatioAtTickHiCall_tick]

def getSqrtRatioSourceTickHiAbsTickInt (I : ExecutionEnv) : Int :=
  if getTickSourceTickHiInt I < 0 then 0 - getTickSourceTickHiInt I
  else getTickSourceTickHiInt I

def getSqrtRatioSourceTickHiAbsTickValue (I : ExecutionEnv) : Value :=
  .int (getSqrtRatioSourceTickHiAbsTickInt I)

def getSqrtRatioStoreAfterTickHiAbsTick (I : ExecutionEnv) : Store :=
  (getTickStoreForSqrtRatioAtTickHiCall I).insert "absTick"
    (getSqrtRatioSourceTickHiAbsTickValue I)

theorem getSqrtRatioStoreAfterTickHiAbsTick_absTick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiAbsTick I).get? "absTick" =
      some (getSqrtRatioSourceTickHiAbsTickValue I) := by
  rw [getSqrtRatioStoreAfterTickHiAbsTick, store_get_self]

theorem getSqrtRatioStoreAfterTickHiAbsTick_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiAbsTick I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  rw [getSqrtRatioStoreAfterTickHiAbsTick]
  rw [store_get_ne (getTickStoreForSqrtRatioAtTickHiCall I) (k := "absTick")
    (a := "tick") (getSqrtRatioSourceTickHiAbsTickValue I) (by decide)]
  exact getTickStoreForSqrtRatioAtTickHiCall_tick I

theorem evalExpr_getSqrtRatio_absTick_forTickHi {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
        { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I }
        evm
        (.ite (ltE (.var "tick") (.intLit 0))
          (subE (.intLit 0) (.var "tick"))
          (.var "tick")) = .ok (getSqrtRatioSourceTickHiAbsTickValue I) := by
  unfold getSqrtRatioSourceTickHiAbsTickValue getSqrtRatioSourceTickHiAbsTickInt ltE subE
  by_cases hneg : getTickSourceTickHiInt I < 0
  · simp [evalExpr?, evalExpr_getSqrtRatio_tickVar_forTickHi, EvalResult.bind, bind,
      pure, evalBinaryOp?, getTickSourceTickHiValue, hneg]
  · simp [evalExpr?, evalExpr_getSqrtRatio_tickVar_forTickHi, EvalResult.bind, bind,
      pure, evalBinaryOp?, getTickSourceTickHiValue, hneg]

theorem evalExpr_getSqrtRatio_absTickVar_forTickHi {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
        { contract := contract v, locals := getSqrtRatioStoreAfterTickHiAbsTick I }
        evm (.var "absTick") = .ok (getSqrtRatioSourceTickHiAbsTickValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getSqrtRatioStoreAfterTickHiAbsTick_absTick]

theorem evalExpr_getSqrtRatio_absTickLeMax_forTickHi {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    evalExpr? (config v)
        { contract := contract v, locals := getSqrtRatioStoreAfterTickHiAbsTick I }
        evm (leE (.var "absTick") maxTick) = .ok (.bool true) := by
  unfold leE maxTick
  simp [evalExpr?, evalExpr_getSqrtRatio_absTickVar_forTickHi, EvalResult.bind, bind,
    pure, evalBinaryOp?, getSqrtRatioSourceTickHiAbsTickValue, hrange]

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiAbsTickPrefix
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      [ .letDecl "absTick" (some uint256)
          (.ite (ltE (.var "tick") (.intLit 0))
            (subE (.intLit 0) (.var "tick"))
            (.var "tick")),
        .require (leE (.var "absTick") maxTick) ]
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiAbsTick I } evm) := by
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_getSqrtRatio_absTick_forTickHi evm I)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_getSqrtRatio_absTickLeMax_forTickHi evm I hrange))
    ExecBlock.nil

def getSqrtRatioSourceTickHiBit1Int (I : ExecutionEnv) : Int :=
  Nat.land (getSqrtRatioSourceTickHiAbsTickInt I).toNat 1

def getSqrtRatioSourceTickHiInitialRatioInt (I : ExecutionEnv) : Int :=
  if getSqrtRatioSourceTickHiBit1Int I = 0 then 2 ^ (128 : Nat)
  else 340265354078544963557816517032075149313

def getSqrtRatioSourceTickHiInitialRatioValue (I : ExecutionEnv) : Value :=
  .int (getSqrtRatioSourceTickHiInitialRatioInt I)

def getSqrtRatioStoreAfterTickHiInitialRatio (I : ExecutionEnv) : Store :=
  (getSqrtRatioStoreAfterTickHiAbsTick I).insert "ratio"
    (getSqrtRatioSourceTickHiInitialRatioValue I)

theorem getSqrtRatioSourceTickHiAbsTickInt_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAbsTickInt I := by
  unfold getSqrtRatioSourceTickHiAbsTickInt
  by_cases h : getTickSourceTickHiInt I < 0 <;> omega

theorem getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus
    (I : ExecutionEnv) (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    getSqrtRatioSourceTickHiAbsTickInt I < (EVM.wordModulus : Int) := by
  norm_num [EVM.wordModulus, EVM.twoPow]
  omega

theorem evalExpr_getSqrtRatio_absTickBit1_forTickHi {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    evalExpr? (config v)
        { contract := contract v, locals := getSqrtRatioStoreAfterTickHiAbsTick I }
        evm (bitAndE (.var "absTick") (.intLit 1)) =
      .ok (.int (getSqrtRatioSourceTickHiBit1Int I)) := by
  unfold bitAndE getSqrtRatioSourceTickHiBit1Int
  have hnonneg := getSqrtRatioSourceTickHiAbsTickInt_nonneg I
  have hlt := getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I hrange
  have hone : 1 < EVM.wordModulus := by norm_num [EVM.wordModulus, EVM.twoPow]
  simp [evalExpr?, evalExpr_getSqrtRatio_absTickVar_forTickHi, EvalResult.bind, bind,
    pure, evalBinaryOp?, getSqrtRatioSourceTickHiAbsTickValue, hnonneg, hlt, hone]

theorem evalExpr_getSqrtRatio_initialRatio_forTickHi {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    evalExpr? (config v)
        { contract := contract v, locals := getSqrtRatioStoreAfterTickHiAbsTick I }
        evm
        (.ite (neE (bitAndE (.var "absTick") (.intLit 0x1)) (.intLit 0))
          (.intLit 0xfffcb933bd6fad37aa2d162d1a594001)
          fixedPoint128Q128) =
      .ok (getSqrtRatioSourceTickHiInitialRatioValue I) := by
  unfold getSqrtRatioSourceTickHiInitialRatioValue getSqrtRatioSourceTickHiInitialRatioInt
    neE fixedPoint128Q128
  by_cases hzero : getSqrtRatioSourceTickHiBit1Int I = 0
  · simp [evalExpr?, evalExpr_getSqrtRatio_absTickBit1_forTickHi evm I hrange,
      EvalResult.bind, bind, pure, evalBinaryOp?, hzero]
  · have hbeq :
        (Value.int (getSqrtRatioSourceTickHiBit1Int I) == Value.int 0) = false := by
      cases h : (Value.int (getSqrtRatioSourceTickHiBit1Int I) == Value.int 0) <;>
        simp_all
    simp [evalExpr?, evalExpr_getSqrtRatio_absTickBit1_forTickHi evm I hrange,
      EvalResult.bind, bind, pure, evalBinaryOp?, hzero, hbeq]

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiInitialRatioPrefix
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      [ .letDecl "absTick" (some uint256)
          (.ite (ltE (.var "tick") (.intLit 0))
            (subE (.intLit 0) (.var "tick"))
            (.var "tick")),
        .require (leE (.var "absTick") maxTick),
        .letDecl "ratio" (some uint256)
          (.ite (neE (bitAndE (.var "absTick") (.intLit 0x1)) (.intLit 0))
            (.intLit 0xfffcb933bd6fad37aa2d162d1a594001)
            fixedPoint128Q128) ]
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiInitialRatio I }
        evm) := by
  refine execBlock_append
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiAbsTickPrefix evm I hrange) ?_
  exact ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_getSqrtRatio_initialRatio_forTickHi evm I hrange))
    ExecBlock.nil

def getSqrtRatioSourceTickRatioStepBitInt (absTick mask : Int) : Int :=
  Nat.land absTick.toNat mask.toNat

def getSqrtRatioSourceTickRatioStepRatioInt
    (absTick ratio mask constant : Int) : Int :=
  if getSqrtRatioSourceTickRatioStepBitInt absTick mask = 0 then ratio
  else ((ratio * constant).toNat / 2 ^ (128 : Nat) : Nat)

theorem getSqrtRatioSourceTickRatioStepRatioInt_nonneg
    (absTick ratio mask constant : Int)
    (hratio0 : 0 ≤ ratio) :
    0 ≤ getSqrtRatioSourceTickRatioStepRatioInt absTick ratio mask constant := by
  unfold getSqrtRatioSourceTickRatioStepRatioInt
  by_cases h : getSqrtRatioSourceTickRatioStepBitInt absTick mask = 0
  · simp [h, hratio0]
  · simp [h]
    exact Int.ediv_nonneg (le_max_right _ _) (by norm_num)

theorem getSqrtRatioSourceTickRatioStepRatioInt_le_input
    (absTick ratio mask constant : Int)
    (hratio0 : 0 ≤ ratio) (hconst0 : 0 ≤ constant)
    (hconstLe : constant ≤ 2 ^ (128 : Nat)) :
    getSqrtRatioSourceTickRatioStepRatioInt absTick ratio mask constant ≤ ratio := by
  unfold getSqrtRatioSourceTickRatioStepRatioInt
  by_cases h : getSqrtRatioSourceTickRatioStepBitInt absTick mask = 0
  · simp [h]
  · simp [h]
    apply Int.ediv_le_of_le_mul
    · norm_num
    · have hprod0 : 0 ≤ ratio * constant := mul_nonneg hratio0 hconst0
      rw [max_eq_left hprod0]
      exact mul_le_mul_of_nonneg_left hconstLe hratio0

theorem getSqrtRatioSourceTickRatioStepRatioInt_le_q128
    (absTick ratio mask constant : Int)
    (hratio0 : 0 ≤ ratio) (hratioLe : ratio ≤ 2 ^ (128 : Nat))
    (hconst0 : 0 ≤ constant) (hconstLe : constant ≤ 2 ^ (128 : Nat)) :
    getSqrtRatioSourceTickRatioStepRatioInt absTick ratio mask constant ≤
      2 ^ (128 : Nat) := by
  exact le_trans
    (getSqrtRatioSourceTickRatioStepRatioInt_le_input absTick ratio mask constant
      hratio0 hconst0 hconstLe)
    hratioLe

theorem getSqrtRatioSourceRatio_mul_lt_wordModulus
    (ratio constant : Int)
    (hratioLe : ratio ≤ 2 ^ (128 : Nat))
    (hconst0 : 0 ≤ constant) (hconstLt : constant < 2 ^ (128 : Nat)) :
    ratio * constant < (EVM.wordModulus : Int) := by
  have hconstLe : constant ≤ (2 ^ (128 : Nat) : Int) - 1 := by omega
  have hmulLe :
      ratio * constant ≤ (2 ^ (128 : Nat) : Int) *
        ((2 ^ (128 : Nat) : Int) - 1) := by
    exact mul_le_mul hratioLe hconstLe hconst0 (by positivity)
  have hcap :
      (2 ^ (128 : Nat) : Int) * ((2 ^ (128 : Nat) : Int) - 1) <
        (EVM.wordModulus : Int) := by
    norm_num [EVM.wordModulus, EVM.twoPow]
  omega

def getSqrtRatioSourceTickRatioStepStoreAfter
    (S : Store) (absTick ratio mask constant : Int) : Store :=
  if getSqrtRatioSourceTickRatioStepBitInt absTick mask = 0 then S
  else
    S.insert "ratio"
      (.int (getSqrtRatioSourceTickRatioStepRatioInt absTick ratio mask constant))

theorem evalExpr_getSqrtRatio_absTickVar
    {v : PoolImmutables} (evm : EVM.State) (S : Store) (absTick : Int)
    (habs : S.get? "absTick" = some (.int absTick)) :
    evalExpr? (config v) { contract := contract v, locals := S } evm (.var "absTick") =
      .ok (.int absTick) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [habs]

theorem evalExpr_getSqrtRatio_ratioVar
    {v : PoolImmutables} (evm : EVM.State) (S : Store) (ratio : Int)
    (hratio : S.get? "ratio" = some (.int ratio)) :
    evalExpr? (config v) { contract := contract v, locals := S } evm (.var "ratio") =
      .ok (.int ratio) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [hratio]

theorem evalExpr_getSqrtRatio_var_of_get
    {v : PoolImmutables} (evm : EVM.State) (S : Store) (key : Ident) (value : Value)
    (hget : S.get? key = some value) :
    evalExpr? (config v) { contract := contract v, locals := S } evm (.var key) =
      .ok value := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [hget]

theorem evalExpr_getSqrtRatio_tickRatioStepBit
    {v : PoolImmutables} (evm : EVM.State) (S : Store) (absTick mask : Int)
    (habs : S.get? "absTick" = some (.int absTick))
    (habs0 : 0 ≤ absTick) (habsLt : absTick < (EVM.wordModulus : Int))
    (hmask0 : 0 ≤ mask) (hmaskLt : mask < (EVM.wordModulus : Int)) :
    evalExpr? (config v) { contract := contract v, locals := S } evm
        (bitAndE (.var "absTick") (.intLit mask)) =
      .ok (.int (getSqrtRatioSourceTickRatioStepBitInt absTick mask)) := by
  unfold bitAndE getSqrtRatioSourceTickRatioStepBitInt
  simp [evalExpr?, evalExpr_getSqrtRatio_absTickVar (v := v) evm S absTick habs,
    EvalResult.bind, bind, pure, evalBinaryOp?, habs0, habsLt, hmask0, hmaskLt]

theorem evalExpr_getSqrtRatio_tickRatioStepCond
    {v : PoolImmutables} (evm : EVM.State) (S : Store) (absTick mask : Int)
    (habs : S.get? "absTick" = some (.int absTick))
    (habs0 : 0 ≤ absTick) (habsLt : absTick < (EVM.wordModulus : Int))
    (hmask0 : 0 ≤ mask) (hmaskLt : mask < (EVM.wordModulus : Int)) :
    evalExpr? (config v) { contract := contract v, locals := S } evm
        (neE (bitAndE (.var "absTick") (.intLit mask)) (.intLit 0)) =
      .ok (.bool (!(Value.int (getSqrtRatioSourceTickRatioStepBitInt absTick mask) ==
        Value.int 0))) := by
  unfold neE
  simp [evalExpr?,
    evalExpr_getSqrtRatio_tickRatioStepBit (v := v) evm S absTick mask habs
      habs0 habsLt hmask0 hmaskLt,
    EvalResult.bind, bind, pure, evalBinaryOp?]

theorem evalExpr_getSqrtRatio_tickRatioStepAssign
    {v : PoolImmutables} (evm : EVM.State) (S : Store) (ratio constant : Int)
    (hratio : S.get? "ratio" = some (.int ratio))
    (hmul0 : 0 ≤ ratio * constant)
    (hmulLt : ratio * constant < (EVM.wordModulus : Int)) :
    evalExpr? (config v) { contract := contract v, locals := S } evm
        (shrE (mulE (.var "ratio") (.intLit constant)) shift128) =
      .ok (.int ((ratio * constant).toNat / 2 ^ (128 : Nat) : Nat)) := by
  unfold shrE mulE shift128
  simp only [evalExpr?, evalExpr_getSqrtRatio_ratioVar (v := v) evm S ratio hratio,
    EvalResult.bind, bind, pure]
  change evalBinaryOp? .shr (.int (ratio * constant)) (.int 128) =
    .ok (.int ((ratio * constant).toNat / 2 ^ (128 : Nat) : Nat))
  rw [evalBinaryOp_int_shr_ok]
  · rfl
  · exact hmul0
  · exact hmulLt
  · norm_num
  · norm_num

set_option maxRecDepth 4096 in
theorem getSqrtRatioSourceTickRatioStepExec
    {v : PoolImmutables} (evm : EVM.State)
    (S : Store) (absTick ratio mask constant : Int)
    (habs : S.get? "absTick" = some (.int absTick))
    (hratio : S.get? "ratio" = some (.int ratio))
    (habs0 : 0 ≤ absTick) (habsLt : absTick < (EVM.wordModulus : Int))
    (hmask0 : 0 ≤ mask) (hmaskLt : mask < (EVM.wordModulus : Int))
    (hmul0 : 0 ≤ ratio * constant)
    (hmulLt : ratio * constant < (EVM.wordModulus : Int)) :
    ExecBlock (config v) { contract := contract v, locals := S } evm
      (tickRatioStep mask constant)
      (.ok
        { contract := contract v,
          locals := getSqrtRatioSourceTickRatioStepStoreAfter S absTick ratio mask constant }
        evm) := by
  unfold tickRatioStep
  by_cases hzero : getSqrtRatioSourceTickRatioStepBitInt absTick mask = 0
  · refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ?_) ExecBlock.nil
    · have hcond :=
        evalExpr_getSqrtRatio_tickRatioStepCond (v := v) evm S absTick mask habs
          habs0 habsLt hmask0 hmaskLt
      rw [hcond]
      simp [hzero]
    · simpa [getSqrtRatioSourceTickRatioStepStoreAfter, hzero] using
        (ExecBlock.nil :
          ExecBlock (config v) { contract := contract v, locals := S } evm []
            (.ok { contract := contract v, locals := S } evm))
  · refine ExecBlock.consNormal (ExecStmt.iteTrue ?_ ?_) ExecBlock.nil
    · have hcond :=
        evalExpr_getSqrtRatio_tickRatioStepCond (v := v) evm S absTick mask habs
          habs0 habsLt hmask0 hmaskLt
      rw [hcond]
      have hbeq :
          (Value.int (getSqrtRatioSourceTickRatioStepBitInt absTick mask) ==
            Value.int 0) = false := by
        cases h : (Value.int (getSqrtRatioSourceTickRatioStepBitInt absTick mask) ==
            Value.int 0) <;> simp_all
      simp [hbeq]
    · refine ExecBlock.consNormal
        (ExecStmt.assign
          (evalExpr_getSqrtRatio_tickRatioStepAssign (v := v) evm S ratio constant
            hratio hmul0 hmulLt) ?_)
        ExecBlock.nil
      unfold assignStorageRef?
      simp only [varRef]
      rw [hratio]
      simp [updateLocalPath?, getSqrtRatioSourceTickRatioStepStoreAfter,
        getSqrtRatioSourceTickRatioStepRatioInt, hzero, EvalResult.bind, bind, pure]

theorem getSqrtRatioSourceTickRatioStepExecOfBounded
    {v : PoolImmutables} (evm : EVM.State)
    (S : Store) (absTick ratio mask constant : Int)
    (habs : S.get? "absTick" = some (.int absTick))
    (hratio : S.get? "ratio" = some (.int ratio))
    (habs0 : 0 ≤ absTick) (habsLt : absTick < (EVM.wordModulus : Int))
    (hmask0 : 0 ≤ mask) (hmaskLt : mask < (EVM.wordModulus : Int))
    (hratio0 : 0 ≤ ratio) (hratioLe : ratio ≤ 2 ^ (128 : Nat))
    (hconst0 : 0 ≤ constant) (hconstLt : constant < 2 ^ (128 : Nat)) :
    ExecBlock (config v) { contract := contract v, locals := S } evm
      (tickRatioStep mask constant)
      (.ok
        { contract := contract v,
          locals := getSqrtRatioSourceTickRatioStepStoreAfter S absTick ratio mask constant }
        evm) := by
  exact getSqrtRatioSourceTickRatioStepExec (v := v) evm S absTick ratio mask constant
    habs hratio habs0 habsLt hmask0 hmaskLt
    (mul_nonneg hratio0 hconst0)
    (getSqrtRatioSourceRatio_mul_lt_wordModulus ratio constant hratioLe hconst0 hconstLt)

theorem getSqrtRatioSourceTickRatioStepStoreAfter_absTick
    (S : Store) (absTick ratio mask constant : Int)
    (habs : S.get? "absTick" = some (.int absTick)) :
    (getSqrtRatioSourceTickRatioStepStoreAfter S absTick ratio mask constant).get?
        "absTick" =
      some (.int absTick) := by
  unfold getSqrtRatioSourceTickRatioStepStoreAfter
  by_cases hzero : getSqrtRatioSourceTickRatioStepBitInt absTick mask = 0
  · rw [if_pos hzero]
    exact habs
  · rw [if_neg hzero]
    rw [store_get_ne S (k := "ratio") (a := "absTick")
      (.int (getSqrtRatioSourceTickRatioStepRatioInt absTick ratio mask constant))
      (by decide)]
    exact habs

theorem getSqrtRatioSourceTickRatioStepStoreAfter_ratio
    (S : Store) (absTick ratio mask constant : Int)
    (hratio : S.get? "ratio" = some (.int ratio)) :
    (getSqrtRatioSourceTickRatioStepStoreAfter S absTick ratio mask constant).get? "ratio" =
      some (.int (getSqrtRatioSourceTickRatioStepRatioInt absTick ratio mask constant)) := by
  unfold getSqrtRatioSourceTickRatioStepStoreAfter
  by_cases hzero : getSqrtRatioSourceTickRatioStepBitInt absTick mask = 0
  · rw [if_pos hzero]
    simpa [getSqrtRatioSourceTickRatioStepRatioInt, hzero] using hratio
  · rw [if_neg hzero]
    rw [store_get_self]

theorem getSqrtRatioSourceTickRatioStepStoreAfter_preserve_of_ne
    (S : Store) (absTick ratio mask constant : Int) (key : Ident)
    (hkey : ("ratio" == key) = false) :
    (getSqrtRatioSourceTickRatioStepStoreAfter S absTick ratio mask constant).get? key =
      S.get? key := by
  unfold getSqrtRatioSourceTickRatioStepStoreAfter
  by_cases hzero : getSqrtRatioSourceTickRatioStepBitInt absTick mask = 0
  · rw [if_pos hzero]
  · rw [if_neg hzero]
    rw [store_get_ne S (k := "ratio") (a := key)
      (.int (getSqrtRatioSourceTickRatioStepRatioInt absTick ratio mask constant))
      hkey]

theorem getSqrtRatioStoreAfterTickHiInitialRatio_absTick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiInitialRatio I).get? "absTick" =
      some (getSqrtRatioSourceTickHiAbsTickValue I) := by
  rw [getSqrtRatioStoreAfterTickHiInitialRatio]
  rw [store_get_ne (getSqrtRatioStoreAfterTickHiAbsTick I) (k := "ratio")
    (a := "absTick") (getSqrtRatioSourceTickHiInitialRatioValue I) (by decide)]
  exact getSqrtRatioStoreAfterTickHiAbsTick_absTick I

theorem getSqrtRatioStoreAfterTickHiInitialRatio_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiInitialRatio I).get? "ratio" =
      some (getSqrtRatioSourceTickHiInitialRatioValue I) := by
  rw [getSqrtRatioStoreAfterTickHiInitialRatio, store_get_self]

theorem getSqrtRatioStoreAfterTickHiInitialRatio_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiInitialRatio I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  rw [getSqrtRatioStoreAfterTickHiInitialRatio]
  rw [store_get_ne (getSqrtRatioStoreAfterTickHiAbsTick I) (k := "ratio")
    (a := "tick") (getSqrtRatioSourceTickHiInitialRatioValue I) (by decide)]
  exact getSqrtRatioStoreAfterTickHiAbsTick_tick I

def getSqrtRatioSourceFactor2Int : Int :=
  340248342086729790484326174814286782778

def getSqrtRatioSourceTickHiAfterBit2Int (I : ExecutionEnv) : Int :=
  getSqrtRatioSourceTickRatioStepRatioInt
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiInitialRatioInt I)
    2
    getSqrtRatioSourceFactor2Int

def getSqrtRatioStoreAfterTickHiBit2 (I : ExecutionEnv) : Store :=
  getSqrtRatioSourceTickRatioStepStoreAfter
    (getSqrtRatioStoreAfterTickHiInitialRatio I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiInitialRatioInt I)
    2
    getSqrtRatioSourceFactor2Int

theorem getSqrtRatioSourceTickHiInitialRatioInt_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiInitialRatioInt I := by
  unfold getSqrtRatioSourceTickHiInitialRatioInt
  by_cases h : getSqrtRatioSourceTickHiBit1Int I = 0 <;> simp [h]

theorem getSqrtRatioSourceTickHiInitialRatioInt_le_q128 (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiInitialRatioInt I ≤ 2 ^ (128 : Nat) := by
  unfold getSqrtRatioSourceTickHiInitialRatioInt
  by_cases h : getSqrtRatioSourceTickHiBit1Int I = 0 <;> simp [h]

theorem getSqrtRatioSourceTickHiAfterBit2Int_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit2Int I := by
  simpa [getSqrtRatioSourceTickHiAfterBit2Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_nonneg
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiInitialRatioInt I)
      2
      getSqrtRatioSourceFactor2Int
      (getSqrtRatioSourceTickHiInitialRatioInt_nonneg I)

theorem getSqrtRatioSourceTickHiAfterBit2Int_le_q128 (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit2Int I ≤ 2 ^ (128 : Nat) := by
  simpa [getSqrtRatioSourceTickHiAfterBit2Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_le_q128
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiInitialRatioInt I)
      2
      getSqrtRatioSourceFactor2Int
      (getSqrtRatioSourceTickHiInitialRatioInt_nonneg I)
      (getSqrtRatioSourceTickHiInitialRatioInt_le_q128 I)
      (by norm_num [getSqrtRatioSourceFactor2Int])
      (by norm_num [getSqrtRatioSourceFactor2Int])

theorem getSqrtRatioSourceTickHiInitialRatio_mul_factor2_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiInitialRatioInt I * getSqrtRatioSourceFactor2Int := by
  have h0 := getSqrtRatioSourceTickHiInitialRatioInt_nonneg I
  unfold getSqrtRatioSourceFactor2Int
  positivity

theorem getSqrtRatioSourceTickHiInitialRatio_mul_factor2_lt_wordModulus
    (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiInitialRatioInt I * getSqrtRatioSourceFactor2Int <
      (EVM.wordModulus : Int) := by
  unfold getSqrtRatioSourceTickHiInitialRatioInt getSqrtRatioSourceFactor2Int
  by_cases h : getSqrtRatioSourceTickHiBit1Int I = 0
  · simp [h, EVM.wordModulus, EVM.twoPow]
  · simp [h, EVM.wordModulus, EVM.twoPow]

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit2
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getSqrtRatioStoreAfterTickHiInitialRatio I } evm
      (tickRatioStep 0x2 0xfff97272373d413259a46990580e213a)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit2 I } evm) := by
  exact getSqrtRatioSourceTickRatioStepExec (v := v) evm
    (getSqrtRatioStoreAfterTickHiInitialRatio I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiInitialRatioInt I)
    2
    getSqrtRatioSourceFactor2Int
    (by
      simpa [getSqrtRatioSourceTickHiAbsTickValue] using
        getSqrtRatioStoreAfterTickHiInitialRatio_absTick I)
    (by
      simpa [getSqrtRatioSourceTickHiInitialRatioValue] using
        getSqrtRatioStoreAfterTickHiInitialRatio_ratio I)
    (getSqrtRatioSourceTickHiAbsTickInt_nonneg I)
    (getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I hrange)
    (by norm_num)
    (by norm_num [EVM.wordModulus, EVM.twoPow])
    (getSqrtRatioSourceTickHiInitialRatio_mul_factor2_nonneg I)
    (getSqrtRatioSourceTickHiInitialRatio_mul_factor2_lt_wordModulus I)

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit2
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      ([ .letDecl "absTick" (some uint256)
          (.ite (ltE (.var "tick") (.intLit 0))
            (subE (.intLit 0) (.var "tick"))
            (.var "tick")),
        .require (leE (.var "absTick") maxTick),
        .letDecl "ratio" (some uint256)
          (.ite (neE (bitAndE (.var "absTick") (.intLit 0x1)) (.intLit 0))
            (.intLit 0xfffcb933bd6fad37aa2d162d1a594001)
            fixedPoint128Q128) ] ++
        tickRatioStep 0x2 0xfff97272373d413259a46990580e213a)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit2 I }
        evm) := by
  exact execBlock_append
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiInitialRatioPrefix evm I hrange)
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit2 evm I hrange)

theorem getSqrtRatioStoreAfterTickHiBit2_absTick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit2 I).get? "absTick" =
      some (getSqrtRatioSourceTickHiAbsTickValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit2, getSqrtRatioSourceTickHiAbsTickValue] using
    getSqrtRatioSourceTickRatioStepStoreAfter_absTick
      (getSqrtRatioStoreAfterTickHiInitialRatio I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiInitialRatioInt I)
      2
      getSqrtRatioSourceFactor2Int
      (by
        simpa [getSqrtRatioSourceTickHiAbsTickValue] using
          getSqrtRatioStoreAfterTickHiInitialRatio_absTick I)

theorem getSqrtRatioStoreAfterTickHiBit2_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit2 I).get? "ratio" =
      some (.int (getSqrtRatioSourceTickHiAfterBit2Int I)) := by
  simpa [getSqrtRatioStoreAfterTickHiBit2, getSqrtRatioSourceTickHiAfterBit2Int,
    getSqrtRatioSourceTickHiInitialRatioValue] using
    getSqrtRatioSourceTickRatioStepStoreAfter_ratio
      (getSqrtRatioStoreAfterTickHiInitialRatio I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiInitialRatioInt I)
      2
      getSqrtRatioSourceFactor2Int
      (by
        simpa [getSqrtRatioSourceTickHiInitialRatioValue] using
          getSqrtRatioStoreAfterTickHiInitialRatio_ratio I)

theorem getSqrtRatioStoreAfterTickHiBit2_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit2 I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit2] using
    getSqrtRatioSourceTickRatioStepStoreAfter_preserve_of_ne
      (getSqrtRatioStoreAfterTickHiInitialRatio I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiInitialRatioInt I)
      2
      getSqrtRatioSourceFactor2Int
      "tick"
      (by decide) |>.trans (getSqrtRatioStoreAfterTickHiInitialRatio_tick I)

def getSqrtRatioSourceFactor4Int : Int :=
  340214320654664324051920982716015181260

def getSqrtRatioSourceTickHiAfterBit4Int (I : ExecutionEnv) : Int :=
  getSqrtRatioSourceTickRatioStepRatioInt
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit2Int I)
    4
    getSqrtRatioSourceFactor4Int

def getSqrtRatioStoreAfterTickHiBit4 (I : ExecutionEnv) : Store :=
  getSqrtRatioSourceTickRatioStepStoreAfter
    (getSqrtRatioStoreAfterTickHiBit2 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit2Int I)
    4
    getSqrtRatioSourceFactor4Int

theorem getSqrtRatioSourceTickHiAfterBit4Int_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit4Int I := by
  simpa [getSqrtRatioSourceTickHiAfterBit4Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_nonneg
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit2Int I)
      4
      getSqrtRatioSourceFactor4Int
      (getSqrtRatioSourceTickHiAfterBit2Int_nonneg I)

theorem getSqrtRatioSourceTickHiAfterBit4Int_le_q128 (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit4Int I ≤ 2 ^ (128 : Nat) := by
  simpa [getSqrtRatioSourceTickHiAfterBit4Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_le_q128
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit2Int I)
      4
      getSqrtRatioSourceFactor4Int
      (getSqrtRatioSourceTickHiAfterBit2Int_nonneg I)
      (getSqrtRatioSourceTickHiAfterBit2Int_le_q128 I)
      (by norm_num [getSqrtRatioSourceFactor4Int])
      (by norm_num [getSqrtRatioSourceFactor4Int])

theorem getSqrtRatioSourceTickHiAfterBit2_mul_factor4_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit2Int I * getSqrtRatioSourceFactor4Int := by
  unfold getSqrtRatioSourceTickHiAfterBit2Int getSqrtRatioSourceTickRatioStepRatioInt
    getSqrtRatioSourceFactor2Int getSqrtRatioSourceFactor4Int
  by_cases h2 :
      getSqrtRatioSourceTickRatioStepBitInt (getSqrtRatioSourceTickHiAbsTickInt I) 2 = 0
  · simp [h2]
    exact getSqrtRatioSourceTickHiInitialRatioInt_nonneg I
  · simp [h2]
    exact Int.ediv_nonneg (le_max_right _ _) (by norm_num)

theorem getSqrtRatioSourceTickHiAfterBit2_mul_factor4_lt_wordModulus
    (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit2Int I * getSqrtRatioSourceFactor4Int <
      (EVM.wordModulus : Int) := by
  unfold getSqrtRatioSourceTickHiAfterBit2Int getSqrtRatioSourceTickRatioStepRatioInt
    getSqrtRatioSourceFactor2Int getSqrtRatioSourceFactor4Int
    getSqrtRatioSourceTickHiInitialRatioInt
  by_cases h2 :
      getSqrtRatioSourceTickRatioStepBitInt (getSqrtRatioSourceTickHiAbsTickInt I) 2 = 0
  · by_cases h1 : getSqrtRatioSourceTickHiBit1Int I = 0
    · simp [h2, h1, EVM.wordModulus, EVM.twoPow]
    · simp [h2, h1, EVM.wordModulus, EVM.twoPow]
  · by_cases h1 : getSqrtRatioSourceTickHiBit1Int I = 0
    · simp [h2, h1, EVM.wordModulus, EVM.twoPow]
    · simp [h2, h1, EVM.wordModulus, EVM.twoPow]

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit4
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit2 I } evm
      (tickRatioStep 0x4 0xfff2e50f5f656932ef12357cf3c7fdcc)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit4 I } evm) := by
  exact getSqrtRatioSourceTickRatioStepExec (v := v) evm
    (getSqrtRatioStoreAfterTickHiBit2 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit2Int I)
    4
    getSqrtRatioSourceFactor4Int
    (by
      simpa [getSqrtRatioSourceTickHiAbsTickValue] using
        getSqrtRatioStoreAfterTickHiBit2_absTick I)
    (getSqrtRatioStoreAfterTickHiBit2_ratio I)
    (getSqrtRatioSourceTickHiAbsTickInt_nonneg I)
    (getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I hrange)
    (by norm_num)
    (by norm_num [EVM.wordModulus, EVM.twoPow])
    (getSqrtRatioSourceTickHiAfterBit2_mul_factor4_nonneg I)
    (getSqrtRatioSourceTickHiAfterBit2_mul_factor4_lt_wordModulus I)

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit4
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      (([ .letDecl "absTick" (some uint256)
          (.ite (ltE (.var "tick") (.intLit 0))
            (subE (.intLit 0) (.var "tick"))
            (.var "tick")),
        .require (leE (.var "absTick") maxTick),
        .letDecl "ratio" (some uint256)
          (.ite (neE (bitAndE (.var "absTick") (.intLit 0x1)) (.intLit 0))
            (.intLit 0xfffcb933bd6fad37aa2d162d1a594001)
            fixedPoint128Q128) ] ++
        tickRatioStep 0x2 0xfff97272373d413259a46990580e213a) ++
        tickRatioStep 0x4 0xfff2e50f5f656932ef12357cf3c7fdcc)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit4 I }
        evm) := by
  exact execBlock_append
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit2 evm I hrange)
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit4 evm I hrange)

theorem getSqrtRatioStoreAfterTickHiBit4_absTick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit4 I).get? "absTick" =
      some (getSqrtRatioSourceTickHiAbsTickValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit4, getSqrtRatioSourceTickHiAbsTickValue] using
    getSqrtRatioSourceTickRatioStepStoreAfter_absTick
      (getSqrtRatioStoreAfterTickHiBit2 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit2Int I)
      4
      getSqrtRatioSourceFactor4Int
      (by
        simpa [getSqrtRatioSourceTickHiAbsTickValue] using
          getSqrtRatioStoreAfterTickHiBit2_absTick I)

theorem getSqrtRatioStoreAfterTickHiBit4_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit4 I).get? "ratio" =
      some (.int (getSqrtRatioSourceTickHiAfterBit4Int I)) := by
  simpa [getSqrtRatioStoreAfterTickHiBit4, getSqrtRatioSourceTickHiAfterBit4Int] using
    getSqrtRatioSourceTickRatioStepStoreAfter_ratio
      (getSqrtRatioStoreAfterTickHiBit2 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit2Int I)
      4
      getSqrtRatioSourceFactor4Int
      (getSqrtRatioStoreAfterTickHiBit2_ratio I)

theorem getSqrtRatioStoreAfterTickHiBit4_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit4 I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit4] using
    getSqrtRatioSourceTickRatioStepStoreAfter_preserve_of_ne
      (getSqrtRatioStoreAfterTickHiBit2 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit2Int I)
      4
      getSqrtRatioSourceFactor4Int
      "tick"
      (by decide) |>.trans (getSqrtRatioStoreAfterTickHiBit2_tick I)

def getSqrtRatioSourceFactor8Int : Int :=
  340146287995602323631171512101879684304

def getSqrtRatioSourceTickHiAfterBit8Int (I : ExecutionEnv) : Int :=
  getSqrtRatioSourceTickRatioStepRatioInt
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit4Int I)
    8
    getSqrtRatioSourceFactor8Int

def getSqrtRatioStoreAfterTickHiBit8 (I : ExecutionEnv) : Store :=
  getSqrtRatioSourceTickRatioStepStoreAfter
    (getSqrtRatioStoreAfterTickHiBit4 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit4Int I)
    8
    getSqrtRatioSourceFactor8Int

theorem getSqrtRatioSourceTickHiAfterBit4_mul_factor8_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit4Int I * getSqrtRatioSourceFactor8Int := by
  exact mul_nonneg
    (getSqrtRatioSourceTickHiAfterBit4Int_nonneg I)
    (by norm_num [getSqrtRatioSourceFactor8Int])

theorem getSqrtRatioSourceTickHiAfterBit4_mul_factor8_lt_wordModulus
    (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit4Int I * getSqrtRatioSourceFactor8Int <
      (EVM.wordModulus : Int) := by
  exact getSqrtRatioSourceRatio_mul_lt_wordModulus
    (getSqrtRatioSourceTickHiAfterBit4Int I)
    getSqrtRatioSourceFactor8Int
    (getSqrtRatioSourceTickHiAfterBit4Int_le_q128 I)
    (by norm_num [getSqrtRatioSourceFactor8Int])
    (by norm_num [getSqrtRatioSourceFactor8Int])

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit8
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit4 I } evm
      (tickRatioStep 0x8 0xffe5caca7e10e4e61c3624eaa0941cd0)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit8 I } evm) := by
  exact getSqrtRatioSourceTickRatioStepExec (v := v) evm
    (getSqrtRatioStoreAfterTickHiBit4 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit4Int I)
    8
    getSqrtRatioSourceFactor8Int
    (by
      simpa [getSqrtRatioSourceTickHiAbsTickValue] using
        getSqrtRatioStoreAfterTickHiBit4_absTick I)
    (getSqrtRatioStoreAfterTickHiBit4_ratio I)
    (getSqrtRatioSourceTickHiAbsTickInt_nonneg I)
    (getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I hrange)
    (by norm_num)
    (by norm_num [EVM.wordModulus, EVM.twoPow])
    (getSqrtRatioSourceTickHiAfterBit4_mul_factor8_nonneg I)
    (getSqrtRatioSourceTickHiAfterBit4_mul_factor8_lt_wordModulus I)

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit8
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      ((([ .letDecl "absTick" (some uint256)
          (.ite (ltE (.var "tick") (.intLit 0))
            (subE (.intLit 0) (.var "tick"))
            (.var "tick")),
        .require (leE (.var "absTick") maxTick),
        .letDecl "ratio" (some uint256)
          (.ite (neE (bitAndE (.var "absTick") (.intLit 0x1)) (.intLit 0))
            (.intLit 0xfffcb933bd6fad37aa2d162d1a594001)
            fixedPoint128Q128) ] ++
        tickRatioStep 0x2 0xfff97272373d413259a46990580e213a) ++
        tickRatioStep 0x4 0xfff2e50f5f656932ef12357cf3c7fdcc) ++
        tickRatioStep 0x8 0xffe5caca7e10e4e61c3624eaa0941cd0)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit8 I }
        evm) := by
  exact execBlock_append
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit4 evm I hrange)
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit8 evm I hrange)

end Benchmarks.UniswapV3Pool

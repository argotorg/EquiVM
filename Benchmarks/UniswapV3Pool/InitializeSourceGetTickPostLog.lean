import Benchmarks.UniswapV3Pool.InitializeSourceGetTickLogRemaining

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

def getTickSourceLogSqrt10001MultiplierInt : Int :=
  255738958999603826347141

def getTickSourceLogSqrt10001Int (I : ExecutionEnv) : Int :=
  getTickSourceLog2After50Int I * getTickSourceLogSqrt10001MultiplierInt

def getTickSourceLogSqrt10001Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceLogSqrt10001Int I)

def getTickStoreAfterLogSqrt10001 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterLogStep50 I).insert "log_sqrt10001" (getTickSourceLogSqrt10001Value I)

def getTickSourceTickLowOffsetInt : Int :=
  3402992956809132418596140100660247210

def getTickSourceTickHiOffsetInt : Int :=
  291339464771989622907027621153398088495

def getTickSourceFixedPoint128Int : Int :=
  2 ^ (128 : Nat)

def getTickSourceTickLowInt (I : ExecutionEnv) : Int :=
  (getTickSourceLogSqrt10001Int I - getTickSourceTickLowOffsetInt) /
    getTickSourceFixedPoint128Int

def getTickSourceTickLowValue (I : ExecutionEnv) : Value :=
  .int (getTickSourceTickLowInt I)

def getTickStoreAfterTickLowLet (I : ExecutionEnv) : Store :=
  (getTickStoreAfterLogSqrt10001 I).insert "tickLow" (getTickSourceTickLowValue I)

def getTickSourceTickHiInt (I : ExecutionEnv) : Int :=
  (getTickSourceLogSqrt10001Int I + getTickSourceTickHiOffsetInt) /
    getTickSourceFixedPoint128Int

def getTickSourceTickHiValue (I : ExecutionEnv) : Value :=
  .int (getTickSourceTickHiInt I)

def getTickStoreAfterTickHiLet (I : ExecutionEnv) : Store :=
  (getTickStoreAfterTickLowLet I).insert "tickHi" (getTickSourceTickHiValue I)

def getTickSourceSqrtRatioAtTickHiValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (getTickHiSqrtRatioWord I).toNat)

def getTickStoreForSqrtRatioAtTickHiCall (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "tick" (getTickSourceTickHiValue I)

def getTickStoreAfterSqrtRatioAtTickHiCall (I : ExecutionEnv) : Store :=
  (getTickStoreAfterTickHiLet I).insert "sqrtRatioAtTickHi"
    (getTickSourceSqrtRatioAtTickHiValue I)

def getTickSourceFinalReturnExpr : Expr :=
  .ite (eqE (.var "tickLow") (.var "tickHi"))
    (.var "tickLow")
    (.ite (leE (.var "sqrtRatioAtTickHi") (.var "sqrtPriceX96"))
      (.var "tickHi")
      (.var "tickLow"))

def getTickSourceFinalValue (I : ExecutionEnv) : Value :=
  if getTickSourceTickLowValue I == getTickSourceTickHiValue I then
    getTickSourceTickLowValue I
  else if Int.ofNat (getTickHiSqrtRatioWord I).toNat ≤ Int.ofNat (initializeArgWord I).toNat then
    getTickSourceTickHiValue I
  else
    getTickSourceTickLowValue I

theorem getTickStoreAfterLogStep50_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogStep50 I).get? "log_2" =
      some (Value.int (getTickSourceLog2After50Int I)) := by
  rw [getTickStoreAfterLogStep50, getTickSourceLogStepStoreAfterLog2, store_get_self]
  rfl

theorem getTickStoreAfterLogSqrt10001_log (I : ExecutionEnv) :
    (getTickStoreAfterLogSqrt10001 I).get? "log_sqrt10001" =
      some (getTickSourceLogSqrt10001Value I) := by
  rw [getTickStoreAfterLogSqrt10001, store_get_self]

theorem getTickStoreAfterLogSqrt10001_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogSqrt10001 I).get? "log_2" =
      some (Value.int (getTickSourceLog2After50Int I)) := by
  rw [getTickStoreAfterLogSqrt10001]
  rw [store_get_ne (getTickStoreAfterLogStep50 I) (k := "log_sqrt10001") (a := "log_2")
    (getTickSourceLogSqrt10001Value I) (by decide)]
  exact getTickStoreAfterLogStep50_log2 I

theorem getTickStoreAfterLogSqrt10001_sqrtPriceX96_of_logStep50
    (I : ExecutionEnv)
    (hsqrtPrice :
      (getTickStoreAfterLogStep50 I).get? "sqrtPriceX96" = some (initializeArgValue I)) :
    (getTickStoreAfterLogSqrt10001 I).get? "sqrtPriceX96" =
      some (initializeArgValue I) := by
  rw [getTickStoreAfterLogSqrt10001]
  rw [store_get_ne (getTickStoreAfterLogStep50 I) (k := "log_sqrt10001")
    (a := "sqrtPriceX96") (getTickSourceLogSqrt10001Value I) (by decide)]
  exact hsqrtPrice

theorem getTickStoreAfterTickLowLet_log (I : ExecutionEnv) :
    (getTickStoreAfterTickLowLet I).get? "log_sqrt10001" =
      some (getTickSourceLogSqrt10001Value I) := by
  rw [getTickStoreAfterTickLowLet]
  rw [store_get_ne (getTickStoreAfterLogSqrt10001 I) (k := "tickLow")
    (a := "log_sqrt10001") (getTickSourceTickLowValue I) (by decide)]
  exact getTickStoreAfterLogSqrt10001_log I

theorem getTickStoreAfterTickLowLet_tickLow (I : ExecutionEnv) :
    (getTickStoreAfterTickLowLet I).get? "tickLow" =
      some (getTickSourceTickLowValue I) := by
  rw [getTickStoreAfterTickLowLet, store_get_self]

theorem getTickStoreAfterTickLowLet_sqrtPriceX96_of_logStep50
    (I : ExecutionEnv)
    (hsqrtPrice :
      (getTickStoreAfterLogStep50 I).get? "sqrtPriceX96" = some (initializeArgValue I)) :
    (getTickStoreAfterTickLowLet I).get? "sqrtPriceX96" =
      some (initializeArgValue I) := by
  rw [getTickStoreAfterTickLowLet]
  rw [store_get_ne (getTickStoreAfterLogSqrt10001 I) (k := "tickLow")
    (a := "sqrtPriceX96") (getTickSourceTickLowValue I) (by decide)]
  exact getTickStoreAfterLogSqrt10001_sqrtPriceX96_of_logStep50 I hsqrtPrice

theorem getTickStoreAfterTickHiLet_log (I : ExecutionEnv) :
    (getTickStoreAfterTickHiLet I).get? "log_sqrt10001" =
      some (getTickSourceLogSqrt10001Value I) := by
  rw [getTickStoreAfterTickHiLet]
  rw [store_get_ne (getTickStoreAfterTickLowLet I) (k := "tickHi")
    (a := "log_sqrt10001") (getTickSourceTickHiValue I) (by decide)]
  exact getTickStoreAfterTickLowLet_log I

theorem getTickStoreAfterTickHiLet_tickLow (I : ExecutionEnv) :
    (getTickStoreAfterTickHiLet I).get? "tickLow" =
      some (getTickSourceTickLowValue I) := by
  rw [getTickStoreAfterTickHiLet]
  rw [store_get_ne (getTickStoreAfterTickLowLet I) (k := "tickHi") (a := "tickLow")
    (getTickSourceTickHiValue I) (by decide)]
  exact getTickStoreAfterTickLowLet_tickLow I

theorem getTickStoreAfterTickHiLet_tickHi (I : ExecutionEnv) :
    (getTickStoreAfterTickHiLet I).get? "tickHi" =
      some (getTickSourceTickHiValue I) := by
  rw [getTickStoreAfterTickHiLet, store_get_self]

theorem getTickStoreAfterTickHiLet_sqrtPriceX96_of_logStep50
    (I : ExecutionEnv)
    (hsqrtPrice :
      (getTickStoreAfterLogStep50 I).get? "sqrtPriceX96" = some (initializeArgValue I)) :
    (getTickStoreAfterTickHiLet I).get? "sqrtPriceX96" =
      some (initializeArgValue I) := by
  rw [getTickStoreAfterTickHiLet]
  rw [store_get_ne (getTickStoreAfterTickLowLet I) (k := "tickHi")
    (a := "sqrtPriceX96") (getTickSourceTickHiValue I) (by decide)]
  exact getTickStoreAfterTickLowLet_sqrtPriceX96_of_logStep50 I hsqrtPrice

theorem evalExpr_getTick_tickHiVar_afterTickHi {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterTickHiLet I }
      evm (.var "tickHi") = .ok (getTickSourceTickHiValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterTickHiLet_tickHi]

theorem evalExprs_getTick_tickHiArg_afterTickHi {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExprs? (config v) { contract := contract v, locals := getTickStoreAfterTickHiLet I }
      evm [.var "tickHi"] = .ok [getTickSourceTickHiValue I] := by
  simp only [evalExprs?, evalExpr_getTick_tickHiVar_afterTickHi, EvalResult.bind, bind, pure]

theorem evalBinaryOp_int_eq_ok (x y : Int) :
    evalBinaryOp? .eq (.int x) (.int y) = .ok (.bool ((Value.int x) == Value.int y)) := by
  rfl

theorem evalBinaryOp_int_le_ok (x y : Int) :
    evalBinaryOp? .le (.int x) (.int y) = .ok (.bool (x ≤ y)) := by
  rfl

theorem evalExpr_ite_true {cfg : Config} {solm : Frame} {evm : EVM.State}
    {cond thenExpr elseExpr : Expr} {value : Value}
    (hcond : evalExpr? cfg solm evm cond = .ok (.bool true))
    (hthen : evalExpr? cfg solm evm thenExpr = .ok value) :
    evalExpr? cfg solm evm (.ite cond thenExpr elseExpr) = .ok value := by
  simp only [evalExpr?, hcond, EvalResult.bind, bind]
  exact hthen

theorem evalExpr_ite_false {cfg : Config} {solm : Frame} {evm : EVM.State}
    {cond thenExpr elseExpr : Expr} {value : Value}
    (hcond : evalExpr? cfg solm evm cond = .ok (.bool false))
    (helse : evalExpr? cfg solm evm elseExpr = .ok value) :
    evalExpr? cfg solm evm (.ite cond thenExpr elseExpr) = .ok value := by
  simp only [evalExpr?, hcond, EvalResult.bind, bind]
  exact helse

theorem getTickStoreAfterSqrtRatioAtTickHiCall_tickLow (I : ExecutionEnv) :
    (getTickStoreAfterSqrtRatioAtTickHiCall I).get? "tickLow" =
      some (getTickSourceTickLowValue I) := by
  rw [getTickStoreAfterSqrtRatioAtTickHiCall]
  rw [store_get_ne (getTickStoreAfterTickHiLet I) (k := "sqrtRatioAtTickHi")
    (a := "tickLow") (getTickSourceSqrtRatioAtTickHiValue I) (by decide)]
  exact getTickStoreAfterTickHiLet_tickLow I

theorem getTickStoreAfterSqrtRatioAtTickHiCall_tickHi (I : ExecutionEnv) :
    (getTickStoreAfterSqrtRatioAtTickHiCall I).get? "tickHi" =
      some (getTickSourceTickHiValue I) := by
  rw [getTickStoreAfterSqrtRatioAtTickHiCall]
  rw [store_get_ne (getTickStoreAfterTickHiLet I) (k := "sqrtRatioAtTickHi")
    (a := "tickHi") (getTickSourceSqrtRatioAtTickHiValue I) (by decide)]
  exact getTickStoreAfterTickHiLet_tickHi I

set_option maxRecDepth 4096 in
theorem getTickStoreAfterSqrtRatioAtTickHiCall_sqrtRatioAtTickHi (I : ExecutionEnv) :
    (getTickStoreAfterSqrtRatioAtTickHiCall I).get? "sqrtRatioAtTickHi" =
      some (getTickSourceSqrtRatioAtTickHiValue I) := by
  rw [getTickStoreAfterSqrtRatioAtTickHiCall, store_get_self]

theorem getTickStoreAfterSqrtRatioAtTickHiCall_sqrtPriceX96_of_logStep50
    (I : ExecutionEnv)
    (hsqrtPrice :
      (getTickStoreAfterLogStep50 I).get? "sqrtPriceX96" = some (initializeArgValue I)) :
    (getTickStoreAfterSqrtRatioAtTickHiCall I).get? "sqrtPriceX96" =
      some (initializeArgValue I) := by
  rw [getTickStoreAfterSqrtRatioAtTickHiCall]
  rw [store_get_ne (getTickStoreAfterTickHiLet I) (k := "sqrtRatioAtTickHi")
    (a := "sqrtPriceX96") (getTickSourceSqrtRatioAtTickHiValue I) (by decide)]
  exact getTickStoreAfterTickHiLet_sqrtPriceX96_of_logStep50 I hsqrtPrice

theorem evalExpr_getTick_tickLowVar_afterSqrtRatioAtTickHiCall
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
      evm (.var "tickLow") = .ok (getTickSourceTickLowValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterSqrtRatioAtTickHiCall_tickLow]

theorem evalExpr_getTick_tickHiVar_afterSqrtRatioAtTickHiCall
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
      evm (.var "tickHi") = .ok (getTickSourceTickHiValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterSqrtRatioAtTickHiCall_tickHi]

theorem evalExpr_getTick_sqrtRatioAtTickHiVar_afterSqrtRatioAtTickHiCall
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
      evm (.var "sqrtRatioAtTickHi") = .ok (getTickSourceSqrtRatioAtTickHiValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterSqrtRatioAtTickHiCall_sqrtRatioAtTickHi]

theorem evalExpr_getTick_sqrtPriceX96Var_afterSqrtRatioAtTickHiCall
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hsqrtPrice :
      (getTickStoreAfterSqrtRatioAtTickHiCall I).get? "sqrtPriceX96" =
        some (initializeArgValue I)) :
    evalExpr? (config v)
      { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
      evm (.var "sqrtPriceX96") = .ok (initializeArgValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [hsqrtPrice]

theorem evalExpr_getTick_tickLowEqTickHi_afterSqrtRatioAtTickHiCall
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
      evm (eqE (.var "tickLow") (.var "tickHi")) =
      .ok (.bool (getTickSourceTickLowValue I == getTickSourceTickHiValue I)) := by
  unfold eqE
  simp only [evalExpr?, evalExpr_getTick_tickLowVar_afterSqrtRatioAtTickHiCall,
    evalExpr_getTick_tickHiVar_afterSqrtRatioAtTickHiCall, EvalResult.bind, bind]
  unfold getTickSourceTickLowValue getTickSourceTickHiValue
  exact evalBinaryOp_int_eq_ok (getTickSourceTickLowInt I) (getTickSourceTickHiInt I)

theorem evalExpr_getTick_sqrtRatioAtTickHiLeSqrtPrice_afterSqrtRatioAtTickHiCall
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hsqrtPrice :
      (getTickStoreAfterSqrtRatioAtTickHiCall I).get? "sqrtPriceX96" =
        some (initializeArgValue I)) :
    evalExpr? (config v)
      { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
      evm (leE (.var "sqrtRatioAtTickHi") (.var "sqrtPriceX96")) =
      .ok (.bool (Int.ofNat (getTickHiSqrtRatioWord I).toNat ≤
        Int.ofNat (initializeArgWord I).toNat)) := by
  unfold leE
  simp only [evalExpr?, evalExpr_getTick_sqrtRatioAtTickHiVar_afterSqrtRatioAtTickHiCall,
    evalExpr_getTick_sqrtPriceX96Var_afterSqrtRatioAtTickHiCall, EvalResult.bind, bind,
    hsqrtPrice]
  unfold getTickSourceSqrtRatioAtTickHiValue initializeArgValue
  exact evalBinaryOp_int_le_ok (Int.ofNat (getTickHiSqrtRatioWord I).toNat)
    (Int.ofNat (initializeArgWord I).toNat)

theorem evalExpr_getTick_finalReturn_afterSqrtRatioAtTickHiCall
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hsqrtPrice :
      (getTickStoreAfterSqrtRatioAtTickHiCall I).get? "sqrtPriceX96" =
        some (initializeArgValue I)) :
    evalExpr? (config v)
      { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
      evm getTickSourceFinalReturnExpr = .ok (getTickSourceFinalValue I) := by
  unfold getTickSourceFinalReturnExpr getTickSourceFinalValue
  by_cases hEq : (getTickSourceTickLowValue I == getTickSourceTickHiValue I) = true
  · rw [if_pos hEq]
    apply evalExpr_ite_true
    · rw [evalExpr_getTick_tickLowEqTickHi_afterSqrtRatioAtTickHiCall]
      exact congrArg (fun b => EvalResult.ok (Value.bool b)) hEq
    · exact evalExpr_getTick_tickLowVar_afterSqrtRatioAtTickHiCall (v := v) evm I
  · have hEqFalse :
        (getTickSourceTickLowValue I == getTickSourceTickHiValue I) = false := by
      cases h : (getTickSourceTickLowValue I == getTickSourceTickHiValue I) <;> simp_all
    rw [if_neg hEq]
    apply evalExpr_ite_false
    · rw [evalExpr_getTick_tickLowEqTickHi_afterSqrtRatioAtTickHiCall]
      exact congrArg (fun b => EvalResult.ok (Value.bool b)) hEqFalse
    · by_cases hLe : Int.ofNat (getTickHiSqrtRatioWord I).toNat ≤
          Int.ofNat (initializeArgWord I).toNat
      · rw [if_pos hLe]
        apply evalExpr_ite_true
        · rw [evalExpr_getTick_sqrtRatioAtTickHiLeSqrtPrice_afterSqrtRatioAtTickHiCall]
          · exact congrArg (fun b => EvalResult.ok (Value.bool b)) (decide_eq_true hLe)
          · exact hsqrtPrice
        · exact evalExpr_getTick_tickHiVar_afterSqrtRatioAtTickHiCall (v := v) evm I
      · rw [if_neg hLe]
        apply evalExpr_ite_false
        · rw [evalExpr_getTick_sqrtRatioAtTickHiLeSqrtPrice_afterSqrtRatioAtTickHiCall]
          · exact congrArg (fun b => EvalResult.ok (Value.bool b)) (decide_eq_false hLe)
          · exact hsqrtPrice
        · exact evalExpr_getTick_tickLowVar_afterSqrtRatioAtTickHiCall (v := v) evm I

theorem evalExpr_getTick_finalReturn_afterSqrtRatioAtTickHiCall_of_eq
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hsqrtPrice :
      (getTickStoreAfterSqrtRatioAtTickHiCall I).get? "sqrtPriceX96" =
        some (initializeArgValue I))
    (hvalue : getTickSourceFinalValue I = initializeTickValue I) :
    evalExpr? (config v)
      { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
      evm getTickSourceFinalReturnExpr = .ok (initializeTickValue I) := by
  rw [← hvalue]
  exact evalExpr_getTick_finalReturn_afterSqrtRatioAtTickHiCall evm I hsqrtPrice

theorem evalExpr_getTick_finalReturn_afterSqrtRatioAtTickHiCall_of_logStep50_eq
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hsqrtPrice :
      (getTickStoreAfterLogStep50 I).get? "sqrtPriceX96" = some (initializeArgValue I))
    (hvalue : getTickSourceFinalValue I = initializeTickValue I) :
    evalExpr? (config v)
      { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
      evm getTickSourceFinalReturnExpr = .ok (initializeTickValue I) := by
  exact evalExpr_getTick_finalReturn_afterSqrtRatioAtTickHiCall_of_eq evm I
    (getTickStoreAfterSqrtRatioAtTickHiCall_sqrtPriceX96_of_logStep50 I hsqrtPrice)
    hvalue

theorem getTickSourceLogStepStoreAfter_preserve_ne (S : Store) (log2 : Int) (r bit : Nat)
    {a : Ident} (hR : ("r" == a) = false) (hF : ("f" == a) = false)
    (hLog2 : ("log_2" == a) = false) :
    (getTickSourceLogStepStoreAfter S log2 r bit).get? a = S.get? a := by
  rw [getTickSourceLogStepStoreAfter]
  rw [store_get_ne (getTickSourceLogStepStoreAfterLog2 S log2 r bit) (k := "r")
    (a := a) (getTickSourceLogStepRAfterValue r) hR]
  rw [getTickSourceLogStepStoreAfterLog2]
  rw [store_get_ne (getTickSourceLogStepStoreAfterFLet S r) (k := "log_2")
    (a := a) (getTickSourceLogStepLog2AfterValue log2 r bit) hLog2]
  rw [getTickSourceLogStepStoreAfterFLet]
  rw [store_get_ne (getTickSourceLogStepStoreAfterRShifted S r) (k := "f")
    (a := a) (getTickSourceLogStepFValue r) hF]
  rw [getTickSourceLogStepStoreAfterRShifted]
  rw [store_get_ne S (k := "r") (a := a) (getTickSourceLogStepRShiftedValue r) hR]

theorem getTickStoreAfterLogStep_preserve_ne (S : Store) (log2 : Int) (r bit : Nat)
    {a : Ident} (hR : ("r" == a) = false) (hF : ("f" == a) = false)
    (hLog2 : ("log_2" == a) = false) :
    (getTickStoreAfterLogStep S log2 r bit).get? a = S.get? a := by
  simpa [getTickStoreAfterLogStep] using
    getTickSourceLogStepStoreAfter_preserve_ne S log2 r bit hR hF hLog2

theorem getTickSourceLogStepStoreAfterLog2_preserve_ne
    (S : Store) (log2 : Int) (r bit : Nat) {a : Ident}
    (hR : ("r" == a) = false) (hF : ("f" == a) = false)
    (hLog2 : ("log_2" == a) = false) :
    (getTickSourceLogStepStoreAfterLog2 S log2 r bit).get? a = S.get? a := by
  rw [getTickSourceLogStepStoreAfterLog2]
  rw [store_get_ne (getTickSourceLogStepStoreAfterFLet S r) (k := "log_2")
    (a := a) (getTickSourceLogStepLog2AfterValue log2 r bit) hLog2]
  rw [getTickSourceLogStepStoreAfterFLet]
  rw [store_get_ne (getTickSourceLogStepStoreAfterRShifted S r) (k := "f")
    (a := a) (getTickSourceLogStepFValue r) hF]
  rw [getTickSourceLogStepStoreAfterRShifted]
  rw [store_get_ne S (k := "r") (a := a) (getTickSourceLogStepRShiftedValue r) hR]

theorem getTickStoreWithMsb_sqrtPriceX96 (I : ExecutionEnv) :
    (getTickStoreWithMsb I).get? "sqrtPriceX96" = some (initializeArgValue I) := by
  rw [getTickStoreWithMsb]
  rw [store_get_ne (getTickStoreWithR I) (k := "msb") (a := "sqrtPriceX96")
    getTickSourceMsbValue (by decide)]
  rw [getTickStoreWithR]
  rw [store_get_ne (getTickStoreWithRatio I) (k := "r") (a := "sqrtPriceX96")
    (getTickSourceRatioValue I) (by decide)]
  rw [getTickStoreWithRatio]
  rw [store_get_ne (initializeStore I) (k := "ratio") (a := "sqrtPriceX96")
    (getTickSourceRatioValue I) (by decide)]
  rw [initializeStore, store_get_self]

theorem getTickStoreAfterMsbCombine_sqrtPriceX96 (I : ExecutionEnv) :
    (getTickStoreAfterMsbCombine I).get? "sqrtPriceX96" =
      some (initializeArgValue I) := by
  rw [getTickStoreAfterMsbCombine]
  rw [store_get_ne (getTickStoreAfterF0Let I) (k := "msb") (a := "sqrtPriceX96")
    (getTickSourceMsbAfter0Value I) (by decide)]
  rw [getTickStoreAfterF0Let]
  rw [store_get_ne (getTickStoreAfterMsbStep1 I) (k := "f") (a := "sqrtPriceX96")
    (getTickSourceMsbF0Value I) (by decide)]
  rw [getTickStoreAfterMsbStep1]
  rw [store_get_ne (getTickStoreAfterMsb1 I) (k := "r") (a := "sqrtPriceX96")
    (getTickSourceRAfterMsb1Value I) (by decide)]
  rw [getTickStoreAfterMsb1]
  rw [store_get_ne (getTickStoreAfterF1Let I) (k := "msb") (a := "sqrtPriceX96")
    (getTickSourceMsbAfter1Value I) (by decide)]
  rw [getTickStoreAfterF1Let]
  rw [store_get_ne (getTickStoreAfterMsbStep2 I) (k := "f") (a := "sqrtPriceX96")
    (getTickSourceMsbF1Value I) (by decide)]
  rw [getTickStoreAfterMsbStep2]
  rw [store_get_ne (getTickStoreAfterMsb2 I) (k := "r") (a := "sqrtPriceX96")
    (getTickSourceRAfterMsb2Value I) (by decide)]
  rw [getTickStoreAfterMsb2]
  rw [store_get_ne (getTickStoreAfterF2Let I) (k := "msb") (a := "sqrtPriceX96")
    (getTickSourceMsbAfter2Value I) (by decide)]
  rw [getTickStoreAfterF2Let]
  rw [store_get_ne (getTickStoreAfterMsbStep3 I) (k := "f") (a := "sqrtPriceX96")
    (getTickSourceMsbF2Value I) (by decide)]
  rw [getTickStoreAfterMsbStep3]
  rw [store_get_ne (getTickStoreAfterMsb3 I) (k := "r") (a := "sqrtPriceX96")
    (getTickSourceRAfterMsb3Value I) (by decide)]
  rw [getTickStoreAfterMsb3]
  rw [store_get_ne (getTickStoreAfterF3Let I) (k := "msb") (a := "sqrtPriceX96")
    (getTickSourceMsbAfter3Value I) (by decide)]
  rw [getTickStoreAfterF3Let]
  rw [store_get_ne (getTickStoreAfterMsbStep4 I) (k := "f") (a := "sqrtPriceX96")
    (getTickSourceMsbF3Value I) (by decide)]
  rw [getTickStoreAfterMsbStep4]
  rw [store_get_ne (getTickStoreAfterMsb4 I) (k := "r") (a := "sqrtPriceX96")
    (getTickSourceRAfterMsb4Value I) (by decide)]
  rw [getTickStoreAfterMsb4]
  rw [store_get_ne (getTickStoreAfterF4Let I) (k := "msb") (a := "sqrtPriceX96")
    (getTickSourceMsbAfter4Value I) (by decide)]
  rw [getTickStoreAfterF4Let]
  rw [store_get_ne (getTickStoreAfterMsbStep5 I) (k := "f") (a := "sqrtPriceX96")
    (getTickSourceMsbF4Value I) (by decide)]
  rw [getTickStoreAfterMsbStep5]
  rw [store_get_ne (getTickStoreAfterMsb5 I) (k := "r") (a := "sqrtPriceX96")
    (getTickSourceRAfterMsb5Value I) (by decide)]
  rw [getTickStoreAfterMsb5]
  rw [store_get_ne (getTickStoreAfterF5Let I) (k := "msb") (a := "sqrtPriceX96")
    (getTickSourceMsbAfter5Value I) (by decide)]
  rw [getTickStoreAfterF5Let]
  rw [store_get_ne (getTickStoreAfterMsbStep6 I) (k := "f") (a := "sqrtPriceX96")
    (getTickSourceMsbF5Value I) (by decide)]
  rw [getTickStoreAfterMsbStep6]
  rw [store_get_ne (getTickStoreAfterMsb6 I) (k := "r") (a := "sqrtPriceX96")
    (getTickSourceRAfterMsb6Value I) (by decide)]
  rw [getTickStoreAfterMsb6]
  rw [store_get_ne (getTickStoreAfterF6Let I) (k := "msb") (a := "sqrtPriceX96")
    (getTickSourceMsbAfter6Value I) (by decide)]
  rw [getTickStoreAfterF6Let]
  rw [store_get_ne (getTickStoreAfterMsbStep7 I) (k := "f") (a := "sqrtPriceX96")
    (getTickSourceMsbF6Value I) (by decide)]
  rw [getTickStoreAfterMsbStep7]
  rw [store_get_ne (getTickStoreAfterMsb7 I) (k := "r") (a := "sqrtPriceX96")
    (getTickSourceRAfterMsb7Value I) (by decide)]
  rw [getTickStoreAfterMsb7]
  rw [store_get_ne (getTickStoreAfterF7Let I) (k := "msb") (a := "sqrtPriceX96")
    (getTickSourceMsbAfter7Value I) (by decide)]
  rw [getTickStoreAfterF7Let]
  rw [store_get_ne (getTickStoreWithMsb I) (k := "f") (a := "sqrtPriceX96")
    (getTickSourceMsbF7Value I) (by decide)]
  exact getTickStoreWithMsb_sqrtPriceX96 I

theorem getTickStoreAfterNormalizeR_sqrtPriceX96 (I : ExecutionEnv) :
    (getTickStoreAfterNormalizeR I).get? "sqrtPriceX96" =
      some (initializeArgValue I) := by
  rw [getTickStoreAfterNormalizeR]
  rw [store_get_ne (getTickStoreAfterMsbCombine I) (k := "r") (a := "sqrtPriceX96")
    (getTickSourceRNormalizedValue I) (by decide)]
  exact getTickStoreAfterMsbCombine_sqrtPriceX96 I

theorem getTickStoreAfterLog2BaseLet_sqrtPriceX96 (I : ExecutionEnv) :
    (getTickStoreAfterLog2BaseLet I).get? "sqrtPriceX96" =
      some (initializeArgValue I) := by
  rw [getTickStoreAfterLog2BaseLet]
  rw [store_get_ne (getTickStoreAfterNormalizeR I) (k := "log_2") (a := "sqrtPriceX96")
    (getTickSourceLog2BaseValue I) (by decide)]
  exact getTickStoreAfterNormalizeR_sqrtPriceX96 I

theorem getTickStoreAfterLogStep63_sqrtPriceX96 (I : ExecutionEnv) :
    (getTickStoreAfterLogStep63 I).get? "sqrtPriceX96" =
      some (initializeArgValue I) := by
  rw [getTickStoreAfterLogStep63]
  rw [store_get_ne (getTickStoreAfterLog2Step63 I) (k := "r") (a := "sqrtPriceX96")
    (getTickSourceLogRAfter63Value I) (by decide)]
  rw [getTickStoreAfterLog2Step63]
  rw [store_get_ne (getTickStoreAfterLogF63Let I) (k := "log_2") (a := "sqrtPriceX96")
    (getTickSourceLog2After63Value I) (by decide)]
  rw [getTickStoreAfterLogF63Let]
  rw [store_get_ne (getTickStoreAfterLogRShifted63 I) (k := "f") (a := "sqrtPriceX96")
    (getTickSourceLogF63Value I) (by decide)]
  rw [getTickStoreAfterLogRShifted63]
  rw [store_get_ne (getTickStoreAfterLog2BaseLet I) (k := "r") (a := "sqrtPriceX96")
    (getTickSourceLogRShifted63Value I) (by decide)]
  exact getTickStoreAfterLog2BaseLet_sqrtPriceX96 I

theorem getTickStoreAfterLogStep62_sqrtPriceX96 (I : ExecutionEnv) :
    (getTickStoreAfterLogStep62 I).get? "sqrtPriceX96" =
      some (initializeArgValue I) := by
  rw [getTickStoreAfterLogStep62]
  rw [store_get_ne (getTickStoreAfterLog2Step62 I) (k := "r") (a := "sqrtPriceX96")
    (getTickSourceLogRAfter62Value I) (by decide)]
  rw [getTickStoreAfterLog2Step62]
  rw [store_get_ne (getTickStoreAfterLogF62Let I) (k := "log_2") (a := "sqrtPriceX96")
    (getTickSourceLog2After62Value I) (by decide)]
  rw [getTickStoreAfterLogF62Let]
  rw [store_get_ne (getTickStoreAfterLogRShifted62 I) (k := "f") (a := "sqrtPriceX96")
    (getTickSourceLogF62Value I) (by decide)]
  rw [getTickStoreAfterLogRShifted62]
  rw [store_get_ne (getTickStoreAfterLogStep63 I) (k := "r") (a := "sqrtPriceX96")
    (getTickSourceLogRShifted62Value I) (by decide)]
  exact getTickStoreAfterLogStep63_sqrtPriceX96 I

theorem getTickStoreAfterLogStep61_sqrtPriceX96 (I : ExecutionEnv) :
    (getTickStoreAfterLogStep61 I).get? "sqrtPriceX96" =
      some (initializeArgValue I) := by
  rw [getTickStoreAfterLogStep61]
  rw [getTickSourceLogStepStoreAfter_preserve_ne]
  exact getTickStoreAfterLogStep62_sqrtPriceX96 I
  all_goals decide

theorem getTickStoreAfterLogStep60_sqrtPriceX96 (I : ExecutionEnv) :
    (getTickStoreAfterLogStep60 I).get? "sqrtPriceX96" =
      some (initializeArgValue I) := by
  rw [getTickStoreAfterLogStep60]
  rw [getTickSourceLogStepStoreAfter_preserve_ne]
  exact getTickStoreAfterLogStep61_sqrtPriceX96 I
  all_goals decide

theorem getTickStoreAfterLogStep59_sqrtPriceX96_of_logStep60
    (I : ExecutionEnv)
    (hsqrtPrice :
      (getTickStoreAfterLogStep60 I).get? "sqrtPriceX96" = some (initializeArgValue I)) :
    (getTickStoreAfterLogStep59 I).get? "sqrtPriceX96" = some (initializeArgValue I) := by
  rw [getTickStoreAfterLogStep59]
  rw [getTickStoreAfterLogStep_preserve_ne]
  exact hsqrtPrice
  all_goals decide

theorem getTickStoreAfterLogStep58_sqrtPriceX96_of_logStep60
    (I : ExecutionEnv)
    (hsqrtPrice :
      (getTickStoreAfterLogStep60 I).get? "sqrtPriceX96" = some (initializeArgValue I)) :
    (getTickStoreAfterLogStep58 I).get? "sqrtPriceX96" = some (initializeArgValue I) := by
  rw [getTickStoreAfterLogStep58]
  rw [getTickStoreAfterLogStep_preserve_ne]
  exact getTickStoreAfterLogStep59_sqrtPriceX96_of_logStep60 I hsqrtPrice
  all_goals decide

theorem getTickStoreAfterLogStep57_sqrtPriceX96_of_logStep60
    (I : ExecutionEnv)
    (hsqrtPrice :
      (getTickStoreAfterLogStep60 I).get? "sqrtPriceX96" = some (initializeArgValue I)) :
    (getTickStoreAfterLogStep57 I).get? "sqrtPriceX96" = some (initializeArgValue I) := by
  rw [getTickStoreAfterLogStep57]
  rw [getTickStoreAfterLogStep_preserve_ne]
  exact getTickStoreAfterLogStep58_sqrtPriceX96_of_logStep60 I hsqrtPrice
  all_goals decide

theorem getTickStoreAfterLogStep56_sqrtPriceX96_of_logStep60
    (I : ExecutionEnv)
    (hsqrtPrice :
      (getTickStoreAfterLogStep60 I).get? "sqrtPriceX96" = some (initializeArgValue I)) :
    (getTickStoreAfterLogStep56 I).get? "sqrtPriceX96" = some (initializeArgValue I) := by
  rw [getTickStoreAfterLogStep56]
  rw [getTickStoreAfterLogStep_preserve_ne]
  exact getTickStoreAfterLogStep57_sqrtPriceX96_of_logStep60 I hsqrtPrice
  all_goals decide

theorem getTickStoreAfterLogStep55_sqrtPriceX96_of_logStep60
    (I : ExecutionEnv)
    (hsqrtPrice :
      (getTickStoreAfterLogStep60 I).get? "sqrtPriceX96" = some (initializeArgValue I)) :
    (getTickStoreAfterLogStep55 I).get? "sqrtPriceX96" = some (initializeArgValue I) := by
  rw [getTickStoreAfterLogStep55]
  rw [getTickStoreAfterLogStep_preserve_ne]
  exact getTickStoreAfterLogStep56_sqrtPriceX96_of_logStep60 I hsqrtPrice
  all_goals decide

theorem getTickStoreAfterLogStep54_sqrtPriceX96_of_logStep60
    (I : ExecutionEnv)
    (hsqrtPrice :
      (getTickStoreAfterLogStep60 I).get? "sqrtPriceX96" = some (initializeArgValue I)) :
    (getTickStoreAfterLogStep54 I).get? "sqrtPriceX96" = some (initializeArgValue I) := by
  rw [getTickStoreAfterLogStep54]
  rw [getTickStoreAfterLogStep_preserve_ne]
  exact getTickStoreAfterLogStep55_sqrtPriceX96_of_logStep60 I hsqrtPrice
  all_goals decide

theorem getTickStoreAfterLogStep53_sqrtPriceX96_of_logStep60
    (I : ExecutionEnv)
    (hsqrtPrice :
      (getTickStoreAfterLogStep60 I).get? "sqrtPriceX96" = some (initializeArgValue I)) :
    (getTickStoreAfterLogStep53 I).get? "sqrtPriceX96" = some (initializeArgValue I) := by
  rw [getTickStoreAfterLogStep53]
  rw [getTickStoreAfterLogStep_preserve_ne]
  exact getTickStoreAfterLogStep54_sqrtPriceX96_of_logStep60 I hsqrtPrice
  all_goals decide

theorem getTickStoreAfterLogStep52_sqrtPriceX96_of_logStep60
    (I : ExecutionEnv)
    (hsqrtPrice :
      (getTickStoreAfterLogStep60 I).get? "sqrtPriceX96" = some (initializeArgValue I)) :
    (getTickStoreAfterLogStep52 I).get? "sqrtPriceX96" = some (initializeArgValue I) := by
  rw [getTickStoreAfterLogStep52]
  rw [getTickStoreAfterLogStep_preserve_ne]
  exact getTickStoreAfterLogStep53_sqrtPriceX96_of_logStep60 I hsqrtPrice
  all_goals decide

theorem getTickStoreAfterLogStep51_sqrtPriceX96_of_logStep60
    (I : ExecutionEnv)
    (hsqrtPrice :
      (getTickStoreAfterLogStep60 I).get? "sqrtPriceX96" = some (initializeArgValue I)) :
    (getTickStoreAfterLogStep51 I).get? "sqrtPriceX96" = some (initializeArgValue I) := by
  rw [getTickStoreAfterLogStep51]
  rw [getTickStoreAfterLogStep_preserve_ne]
  exact getTickStoreAfterLogStep52_sqrtPriceX96_of_logStep60 I hsqrtPrice
  all_goals decide

theorem getTickStoreAfterLogStep50_sqrtPriceX96_of_logStep60
    (I : ExecutionEnv)
    (hsqrtPrice :
      (getTickStoreAfterLogStep60 I).get? "sqrtPriceX96" = some (initializeArgValue I)) :
    (getTickStoreAfterLogStep50 I).get? "sqrtPriceX96" = some (initializeArgValue I) := by
  rw [getTickStoreAfterLogStep50]
  rw [getTickSourceLogStepStoreAfterLog2_preserve_ne]
  exact getTickStoreAfterLogStep51_sqrtPriceX96_of_logStep60 I hsqrtPrice
  all_goals decide

theorem evalExpr_getTick_finalReturn_afterSqrtRatioAtTickHiCall_of_logStep60_eq
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hsqrtPrice :
      (getTickStoreAfterLogStep60 I).get? "sqrtPriceX96" = some (initializeArgValue I))
    (hvalue : getTickSourceFinalValue I = initializeTickValue I) :
    evalExpr? (config v)
      { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
      evm getTickSourceFinalReturnExpr = .ok (initializeTickValue I) := by
  exact evalExpr_getTick_finalReturn_afterSqrtRatioAtTickHiCall_of_logStep50_eq evm I
    (getTickStoreAfterLogStep50_sqrtPriceX96_of_logStep60 I hsqrtPrice)
    hvalue

theorem evalExpr_getTick_finalReturn_afterSqrtRatioAtTickHiCall_of_finalValue_eq
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hvalue : getTickSourceFinalValue I = initializeTickValue I) :
    evalExpr? (config v)
      { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
      evm getTickSourceFinalReturnExpr = .ok (initializeTickValue I) := by
  exact evalExpr_getTick_finalReturn_afterSqrtRatioAtTickHiCall_of_logStep60_eq evm I
    (getTickStoreAfterLogStep60_sqrtPriceX96 I) hvalue

theorem evalExpr_getTick_log2Var_afterLogStep50 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogStep50 I }
      evm (.var "log_2") = .ok (Value.int (getTickSourceLog2After50Int I)) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterLogStep50_log2]

theorem evalExpr_getTick_log_sqrt10001 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogStep50 I }
      evm (mulE (.var "log_2") (.intLit 255738958999603826347141)) =
      .ok (getTickSourceLogSqrt10001Value I) := by
  unfold mulE getTickSourceLogSqrt10001Value getTickSourceLogSqrt10001Int
    getTickSourceLogSqrt10001MultiplierInt
  simp only [evalExpr?, evalExpr_getTick_log2Var_afterLogStep50, EvalResult.bind, bind,
    pure, evalBinaryOp?]

theorem evalExpr_getTick_logSqrtVar_afterLogSqrt {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogSqrt10001 I }
      evm (.var "log_sqrt10001") = .ok (getTickSourceLogSqrt10001Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterLogSqrt10001_log]

theorem evalExpr_getTick_tickLowNumerator {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogSqrt10001 I }
      evm (subE (.var "log_sqrt10001") (.intLit 3402992956809132418596140100660247210)) =
      .ok (.int (getTickSourceLogSqrt10001Int I - getTickSourceTickLowOffsetInt)) := by
  unfold subE getTickSourceTickLowOffsetInt
  simp only [evalExpr?, evalExpr_getTick_logSqrtVar_afterLogSqrt, EvalResult.bind, bind,
    pure, evalBinaryOp?, getTickSourceLogSqrt10001Value]

theorem evalExpr_getTick_tickLow {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogSqrt10001 I }
      evm (divE
        (subE (.var "log_sqrt10001") (.intLit 3402992956809132418596140100660247210))
        fixedPoint128Q128) =
      .ok (getTickSourceTickLowValue I) := by
  unfold divE fixedPoint128Q128 getTickSourceTickLowValue getTickSourceTickLowInt
    getTickSourceFixedPoint128Int
  simp only [evalExpr?, evalExpr_getTick_tickLowNumerator, EvalResult.bind, bind, pure,
    evalBinaryOp?]
  norm_num

theorem evalExpr_getTick_logSqrtVar_afterTickLow {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterTickLowLet I }
      evm (.var "log_sqrt10001") = .ok (getTickSourceLogSqrt10001Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterTickLowLet_log]

theorem evalExpr_getTick_tickHiNumerator {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterTickLowLet I }
      evm (addE (.var "log_sqrt10001") (.intLit 291339464771989622907027621153398088495)) =
      .ok (.int (getTickSourceLogSqrt10001Int I + getTickSourceTickHiOffsetInt)) := by
  unfold addE getTickSourceTickHiOffsetInt
  simp only [evalExpr?, evalExpr_getTick_logSqrtVar_afterTickLow, EvalResult.bind, bind,
    pure, evalBinaryOp?, getTickSourceLogSqrt10001Value]

theorem evalExpr_getTick_tickHi {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterTickLowLet I }
      evm (divE
        (addE (.var "log_sqrt10001") (.intLit 291339464771989622907027621153398088495))
        fixedPoint128Q128) =
      .ok (getTickSourceTickHiValue I) := by
  unfold divE fixedPoint128Q128 getTickSourceTickHiValue getTickSourceTickHiInt
    getTickSourceFixedPoint128Int
  simp only [evalExpr?, evalExpr_getTick_tickHiNumerator, EvalResult.bind, bind, pure,
    evalBinaryOp?]
  norm_num

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogSqrt10001Let {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep50 I }
      evm
      [ .letDecl "log_sqrt10001" (some int256)
          (mulE (.var "log_2") (.intLit 255738958999603826347141)) ]
      (.ok { contract := contract v, locals := getTickStoreAfterLogSqrt10001 I } evm) := by
  exact ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_getTick_log_sqrt10001 evm I))
    ExecBlock.nil

theorem uniswapV3PoolGetTickAtSqrtRatioSourceTickLowHiLets {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogSqrt10001 I }
      evm
      [ .letDecl "tickLow" (some int24)
          (divE
            (subE (.var "log_sqrt10001") (.intLit 3402992956809132418596140100660247210))
            fixedPoint128Q128),
        .letDecl "tickHi" (some int24)
          (divE
            (addE (.var "log_sqrt10001") (.intLit 291339464771989622907027621153398088495))
            fixedPoint128Q128) ]
      (.ok { contract := contract v, locals := getTickStoreAfterTickHiLet I } evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_getTick_tickLow evm I)) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_getTick_tickHi evm I)) ExecBlock.nil

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogSteps59To50AndLogSqrt {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep60 I } evm
      (((logStep 59 true ++
        (logStep 58 true ++
        (logStep 57 true ++
        (logStep 56 true ++
        (logStep 55 true ++
        (logStep 54 true ++
        (logStep 53 true ++
        (logStep 52 true ++
        logStep 51 true)))))))) ++
        logStep 50 false) ++
        [ .letDecl "log_sqrt10001" (some int256)
            (mulE (.var "log_2") (.intLit 255738958999603826347141)) ])
      (.ok { contract := contract v, locals := getTickStoreAfterLogSqrt10001 I } evm) := by
  exact execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceLogSteps59To50 evm I)
    (uniswapV3PoolGetTickAtSqrtRatioSourceLogSqrt10001Let evm I)

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogStepsAndTickLowHi {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep60 I } evm
      ((((logStep 59 true ++
        (logStep 58 true ++
        (logStep 57 true ++
        (logStep 56 true ++
        (logStep 55 true ++
        (logStep 54 true ++
        (logStep 53 true ++
        (logStep 52 true ++
        logStep 51 true)))))))) ++
        logStep 50 false) ++
        [ .letDecl "log_sqrt10001" (some int256)
            (mulE (.var "log_2") (.intLit 255738958999603826347141)) ]) ++
        [ .letDecl "tickLow" (some int24)
            (divE
              (subE (.var "log_sqrt10001") (.intLit 3402992956809132418596140100660247210))
              fixedPoint128Q128),
          .letDecl "tickHi" (some int24)
            (divE
              (addE (.var "log_sqrt10001") (.intLit 291339464771989622907027621153398088495))
              fixedPoint128Q128) ])
      (.ok { contract := contract v, locals := getTickStoreAfterTickHiLet I } evm) := by
  exact execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceLogSteps59To50AndLogSqrt evm I)
    (uniswapV3PoolGetTickAtSqrtRatioSourceTickLowHiLets evm I)

theorem uniswapV3PoolGetTickAtSqrtRatioSourceSqrtRatioAtTickHiCall
    {v : PoolImmutables} {evm : EVM.State} {I : ExecutionEnv} {calleeSolm : Frame}
    (hbody :
      ExecFuncBody (config v)
        { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I }
        evm getSqrtRatioAtTickFunction.body
        (.returned calleeSolm evm (some [getTickSourceSqrtRatioAtTickHiValue I]))) :
    ExecStmt (config v) { contract := contract v, locals := getTickStoreAfterTickHiLet I }
      evm (.internalCall "getSqrtRatioAtTick" [.var "tickHi"] "sqrtRatioAtTickHi")
      (.ok { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
        evm) := by
  have hstmt := internalCallFunctionReturn
    (cfg := config v)
    (caller := { contract := contract v, locals := getTickStoreAfterTickHiLet I })
    (evm := evm) (calleeEvm := evm)
    (name := "getSqrtRatioAtTick") (retVar := "sqrtRatioAtTickHi")
    (args := [.var "tickHi"]) (argVals := [getTickSourceTickHiValue I])
    (callee := getSqrtRatioAtTickFunction)
    (locals := getTickStoreForSqrtRatioAtTickHiCall I)
    (calleeSolm := calleeSolm) (value := some [getTickSourceSqrtRatioAtTickHiValue I])
    (evalExprs_getTick_tickHiArg_afterTickHi evm I)
    (by
      simp [lookupCallable?, lookupFunction?, contract, functions, getSqrtRatioAtTickFunction])
    (by rfl)
    hbody
  simpa [getTickStoreAfterSqrtRatioAtTickHiCall, resumeAfterInternalCall, collapseReturns]
    using hstmt

theorem uniswapV3PoolGetTickAtSqrtRatioSourceSqrtRatioAtTickHiAndReturn
    {v : PoolImmutables} {evm : EVM.State} {I : ExecutionEnv} {calleeSolm : Frame}
    (hbody :
      ExecFuncBody (config v)
        { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I }
        evm getSqrtRatioAtTickFunction.body
        (.returned calleeSolm evm (some [getTickSourceSqrtRatioAtTickHiValue I])))
    (hret :
      evalExpr? (config v)
        { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
        evm getTickSourceFinalReturnExpr = .ok (initializeTickValue I)) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterTickHiLet I } evm
      [ .internalCall "getSqrtRatioAtTick" [.var "tickHi"] "sqrtRatioAtTickHi",
        .return [getTickSourceFinalReturnExpr] ]
      (.returned { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
        evm (some [initializeTickValue I])) := by
  refine ExecBlock.consNormal
    (uniswapV3PoolGetTickAtSqrtRatioSourceSqrtRatioAtTickHiCall
      (v := v) (evm := evm) (I := I) hbody) ?_
  exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hret))

theorem uniswapV3PoolGetTickAtSqrtRatioSourceSqrtRatioAtTickHiAndReturnOfFinalValue
    {v : PoolImmutables} {evm : EVM.State} {I : ExecutionEnv} {calleeSolm : Frame}
    (hbody :
      ExecFuncBody (config v)
        { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I }
        evm getSqrtRatioAtTickFunction.body
        (.returned calleeSolm evm (some [getTickSourceSqrtRatioAtTickHiValue I])))
    (hsqrtPrice :
      (getTickStoreAfterSqrtRatioAtTickHiCall I).get? "sqrtPriceX96" =
        some (initializeArgValue I))
    (hvalue : getTickSourceFinalValue I = initializeTickValue I) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterTickHiLet I } evm
      [ .internalCall "getSqrtRatioAtTick" [.var "tickHi"] "sqrtRatioAtTickHi",
        .return [getTickSourceFinalReturnExpr] ]
      (.returned { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
        evm (some [initializeTickValue I])) := by
  exact uniswapV3PoolGetTickAtSqrtRatioSourceSqrtRatioAtTickHiAndReturn hbody
    (evalExpr_getTick_finalReturn_afterSqrtRatioAtTickHiCall_of_eq evm I hsqrtPrice hvalue)

theorem uniswapV3PoolGetTickAtSqrtRatioSourceSqrtRatioAtTickHiAndReturnOfLogStep50FinalValue
    {v : PoolImmutables} {evm : EVM.State} {I : ExecutionEnv} {calleeSolm : Frame}
    (hbody :
      ExecFuncBody (config v)
        { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I }
        evm getSqrtRatioAtTickFunction.body
        (.returned calleeSolm evm (some [getTickSourceSqrtRatioAtTickHiValue I])))
    (hsqrtPrice :
      (getTickStoreAfterLogStep50 I).get? "sqrtPriceX96" = some (initializeArgValue I))
    (hvalue : getTickSourceFinalValue I = initializeTickValue I) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterTickHiLet I } evm
      [ .internalCall "getSqrtRatioAtTick" [.var "tickHi"] "sqrtRatioAtTickHi",
        .return [getTickSourceFinalReturnExpr] ]
      (.returned { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
        evm (some [initializeTickValue I])) := by
  exact uniswapV3PoolGetTickAtSqrtRatioSourceSqrtRatioAtTickHiAndReturn hbody
    (evalExpr_getTick_finalReturn_afterSqrtRatioAtTickHiCall_of_logStep50_eq evm I
      hsqrtPrice hvalue)

theorem uniswapV3PoolGetTickAtSqrtRatioSourceSqrtRatioAtTickHiAndReturnOfFinalValueEq
    {v : PoolImmutables} {evm : EVM.State} {I : ExecutionEnv} {calleeSolm : Frame}
    (hbody :
      ExecFuncBody (config v)
        { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I }
        evm getSqrtRatioAtTickFunction.body
        (.returned calleeSolm evm (some [getTickSourceSqrtRatioAtTickHiValue I])))
    (hvalue : getTickSourceFinalValue I = initializeTickValue I) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterTickHiLet I } evm
      [ .internalCall "getSqrtRatioAtTick" [.var "tickHi"] "sqrtRatioAtTickHi",
        .return [getTickSourceFinalReturnExpr] ]
      (.returned { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
        evm (some [initializeTickValue I])) := by
  exact uniswapV3PoolGetTickAtSqrtRatioSourceSqrtRatioAtTickHiAndReturn hbody
    (evalExpr_getTick_finalReturn_afterSqrtRatioAtTickHiCall_of_finalValue_eq evm I hvalue)

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogStepsTickLowHiAndReturn
    {v : PoolImmutables} {evm : EVM.State} {I : ExecutionEnv} {calleeSolm : Frame}
    (hbody :
      ExecFuncBody (config v)
        { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I }
        evm getSqrtRatioAtTickFunction.body
        (.returned calleeSolm evm (some [getTickSourceSqrtRatioAtTickHiValue I])))
    (hret :
      evalExpr? (config v)
        { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
        evm getTickSourceFinalReturnExpr = .ok (initializeTickValue I)) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep60 I } evm
      (((((logStep 59 true ++
        (logStep 58 true ++
        (logStep 57 true ++
        (logStep 56 true ++
        (logStep 55 true ++
        (logStep 54 true ++
        (logStep 53 true ++
        (logStep 52 true ++
        logStep 51 true)))))))) ++
        logStep 50 false) ++
        [ .letDecl "log_sqrt10001" (some int256)
            (mulE (.var "log_2") (.intLit 255738958999603826347141)) ]) ++
        [ .letDecl "tickLow" (some int24)
            (divE
              (subE (.var "log_sqrt10001") (.intLit 3402992956809132418596140100660247210))
              fixedPoint128Q128),
          .letDecl "tickHi" (some int24)
            (divE
              (addE (.var "log_sqrt10001") (.intLit 291339464771989622907027621153398088495))
              fixedPoint128Q128) ]) ++
        [ .internalCall "getSqrtRatioAtTick" [.var "tickHi"] "sqrtRatioAtTickHi",
          .return [getTickSourceFinalReturnExpr] ])
      (.returned { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
        evm (some [initializeTickValue I])) := by
  exact execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceLogStepsAndTickLowHi evm I)
    (uniswapV3PoolGetTickAtSqrtRatioSourceSqrtRatioAtTickHiAndReturn hbody hret)

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogStepsTickLowHiAndReturnOfFinalValue
    {v : PoolImmutables} {evm : EVM.State} {I : ExecutionEnv} {calleeSolm : Frame}
    (hbody :
      ExecFuncBody (config v)
        { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I }
        evm getSqrtRatioAtTickFunction.body
        (.returned calleeSolm evm (some [getTickSourceSqrtRatioAtTickHiValue I])))
    (hsqrtPrice :
      (getTickStoreAfterSqrtRatioAtTickHiCall I).get? "sqrtPriceX96" =
        some (initializeArgValue I))
    (hvalue : getTickSourceFinalValue I = initializeTickValue I) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep60 I } evm
      (((((logStep 59 true ++
        (logStep 58 true ++
        (logStep 57 true ++
        (logStep 56 true ++
        (logStep 55 true ++
        (logStep 54 true ++
        (logStep 53 true ++
        (logStep 52 true ++
        logStep 51 true)))))))) ++
        logStep 50 false) ++
        [ .letDecl "log_sqrt10001" (some int256)
            (mulE (.var "log_2") (.intLit 255738958999603826347141)) ]) ++
        [ .letDecl "tickLow" (some int24)
            (divE
              (subE (.var "log_sqrt10001") (.intLit 3402992956809132418596140100660247210))
              fixedPoint128Q128),
          .letDecl "tickHi" (some int24)
            (divE
              (addE (.var "log_sqrt10001") (.intLit 291339464771989622907027621153398088495))
              fixedPoint128Q128) ]) ++
        [ .internalCall "getSqrtRatioAtTick" [.var "tickHi"] "sqrtRatioAtTickHi",
          .return [getTickSourceFinalReturnExpr] ])
      (.returned { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
        evm (some [initializeTickValue I])) := by
  exact uniswapV3PoolGetTickAtSqrtRatioSourceLogStepsTickLowHiAndReturn hbody
    (evalExpr_getTick_finalReturn_afterSqrtRatioAtTickHiCall_of_eq evm I hsqrtPrice hvalue)

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogStepsTickLowHiAndReturnOfLogStep50FinalValue
    {v : PoolImmutables} {evm : EVM.State} {I : ExecutionEnv} {calleeSolm : Frame}
    (hbody :
      ExecFuncBody (config v)
        { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I }
        evm getSqrtRatioAtTickFunction.body
        (.returned calleeSolm evm (some [getTickSourceSqrtRatioAtTickHiValue I])))
    (hsqrtPrice :
      (getTickStoreAfterLogStep50 I).get? "sqrtPriceX96" = some (initializeArgValue I))
    (hvalue : getTickSourceFinalValue I = initializeTickValue I) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep60 I } evm
      (((((logStep 59 true ++
        (logStep 58 true ++
        (logStep 57 true ++
        (logStep 56 true ++
        (logStep 55 true ++
        (logStep 54 true ++
        (logStep 53 true ++
        (logStep 52 true ++
        logStep 51 true)))))))) ++
        logStep 50 false) ++
        [ .letDecl "log_sqrt10001" (some int256)
            (mulE (.var "log_2") (.intLit 255738958999603826347141)) ]) ++
        [ .letDecl "tickLow" (some int24)
            (divE
              (subE (.var "log_sqrt10001") (.intLit 3402992956809132418596140100660247210))
              fixedPoint128Q128),
          .letDecl "tickHi" (some int24)
            (divE
              (addE (.var "log_sqrt10001") (.intLit 291339464771989622907027621153398088495))
              fixedPoint128Q128) ]) ++
        [ .internalCall "getSqrtRatioAtTick" [.var "tickHi"] "sqrtRatioAtTickHi",
          .return [getTickSourceFinalReturnExpr] ])
      (.returned { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
        evm (some [initializeTickValue I])) := by
  exact uniswapV3PoolGetTickAtSqrtRatioSourceLogStepsTickLowHiAndReturn hbody
    (evalExpr_getTick_finalReturn_afterSqrtRatioAtTickHiCall_of_logStep50_eq evm I
      hsqrtPrice hvalue)

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogStepsTickLowHiAndReturnOfFinalValueEq
    {v : PoolImmutables} {evm : EVM.State} {I : ExecutionEnv} {calleeSolm : Frame}
    (hbody :
      ExecFuncBody (config v)
        { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I }
        evm getSqrtRatioAtTickFunction.body
        (.returned calleeSolm evm (some [getTickSourceSqrtRatioAtTickHiValue I])))
    (hvalue : getTickSourceFinalValue I = initializeTickValue I) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep60 I } evm
      (((((logStep 59 true ++
        (logStep 58 true ++
        (logStep 57 true ++
        (logStep 56 true ++
        (logStep 55 true ++
        (logStep 54 true ++
        (logStep 53 true ++
        (logStep 52 true ++
        logStep 51 true)))))))) ++
        logStep 50 false) ++
        [ .letDecl "log_sqrt10001" (some int256)
            (mulE (.var "log_2") (.intLit 255738958999603826347141)) ]) ++
        [ .letDecl "tickLow" (some int24)
            (divE
              (subE (.var "log_sqrt10001") (.intLit 3402992956809132418596140100660247210))
              fixedPoint128Q128),
          .letDecl "tickHi" (some int24)
            (divE
              (addE (.var "log_sqrt10001") (.intLit 291339464771989622907027621153398088495))
              fixedPoint128Q128) ]) ++
        [ .internalCall "getSqrtRatioAtTick" [.var "tickHi"] "sqrtRatioAtTickHi",
          .return [getTickSourceFinalReturnExpr] ])
      (.returned { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
        evm (some [initializeTickValue I])) := by
  exact uniswapV3PoolGetTickAtSqrtRatioSourceLogStepsTickLowHiAndReturn hbody
    (evalExpr_getTick_finalReturn_afterSqrtRatioAtTickHiCall_of_finalValue_eq evm I hvalue)

theorem uniswapV3PoolGetTickAtSqrtRatioSourceSuccessOfSqrtRatioAtTickHi
    {v : PoolImmutables} {evm : EVM.State} {I : ExecutionEnv}
    {calleeSolm : Frame}
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342)
    (hbody :
      ExecFuncBody (config v)
        { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I }
        evm getSqrtRatioAtTickFunction.body
        (.returned calleeSolm evm (some [getTickSourceSqrtRatioAtTickHiValue I])))
    (hvalue : getTickSourceFinalValue I = initializeTickValue I) :
    ExecFuncBody (config v) { contract := contract v, locals := initializeStore I }
      evm getTickAtSqrtRatioFunction.body
      (.returned { contract := contract v, locals := getTickStoreAfterSqrtRatioAtTickHiCall I }
        evm (some [initializeTickValue I])) := by
  refine ExecFuncBody.execBlockRet ?_
  have hprefix := uniswapV3PoolGetTickAtSqrtRatioSourcePrefix (v := v) evm I hlo hhi
  have hthrough60 := uniswapV3PoolGetTickAtSqrtRatioSourceThroughLogStep60 (v := v) evm I
  have htail :=
    uniswapV3PoolGetTickAtSqrtRatioSourceLogStepsTickLowHiAndReturnOfFinalValueEq
      (v := v) (evm := evm) (I := I) hbody hvalue
  simpa [getTickAtSqrtRatioFunction] using execBlock_append hprefix
    (execBlock_append hthrough60 htail)

theorem uniswapV3PoolInitializeSourceSuccessBodyOfSqrtRatioAtTickHi
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256} {calleeSolm : Frame}
    (hwv : I.weiValue = ⟨0⟩)
    (hzero : slot0SqrtPriceX96Word σ I = ⟨0⟩)
    (hlo : 4295128739 ≤ (initializeArgWord I).toNat)
    (hhi : (initializeArgWord I).toNat <
      1461446703485210103287273052203988822378723970342)
    (hbody :
      ExecFuncBody (config v)
        { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I }
        (initState cA gh bl σ σ₀ g A I) getSqrtRatioAtTickFunction.body
        (.returned calleeSolm (initState cA gh bl σ σ₀ g A I)
          (some [getTickSourceSqrtRatioAtTickHiValue I])))
    (hvalue : getTickSourceFinalValue I = initializeTickValue I) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (initializeStore I)
      initializeTransition.body
      (.returned { contract := contract v, locals := initializeStoreWithTickAndTime I }
        (initializeSourceAfterStorageTailState (initState cA gh bl σ σ₀ g A I) I)
        none) := by
  exact uniswapV3PoolInitializeSourceSuccessBodyOfGetTickFunc (v := v) hwv hzero
    (uniswapV3PoolGetTickAtSqrtRatioSourceSuccessOfSqrtRatioAtTickHi
      (v := v) (evm := initState cA gh bl σ σ₀ g A I) (I := I)
      hlo hhi hbody hvalue)

end Benchmarks.UniswapV3Pool

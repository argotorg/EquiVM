import Benchmarks.UniswapV3.Pool.SwapStepPriceCalls
import Benchmarks.UniswapV3.Pool.SwapStepInitialSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def swapStepPriceTest (input : Bool) : Expr :=
  .binary .ge (swapStepChoiceBudgetExpr input) (.var (swapStepAmountName input))

noncomputable def swapStepPriceFrame (imms : Store) (a : SwapStepArgs) (input : Bool) : Frame :=
  {contract := contract
   immutables := imms
   locals := (if swapStepReachTarget a then (swapStepInitialFrame imms a input).locals
     else (swapStepPriceCallFrame imms a input).locals).insert "sqrtRatioNextX96"
       (.int (Int.ofNat (swapStepPrice a).toNat))}

theorem evalSwapStepPriceTest (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (hi : swapStepExactIn a = input) :
    evalExpr? config (swapStepInitialFrame imms a input) evm (swapStepPriceTest input) =
      .ok (.bool (swapStepReachTarget a)) := by
  have hb := evalSwapStepChoiceBudget imms evm a input hi
  have ha := evalExpr_var_get (cfg := config) (evm := evm) (swapStepInitialAmountGet imms a input)
  simp only [swapStepPriceTest, evalExpr?, hb, ha, evalBinaryOp?, bind, EvalResult.bind,
    swapStepReachTarget, swapStepInitialDelta, swapStepInitialAmount, hi]
  apply congrArg (fun b : Bool ↦ EvalResult.ok (Value.bool b))
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact Int.ofNat_le

theorem swapStepTargetAssign (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (hr : swapStepReachTarget a = true) :
    ExecStmt config (swapStepInitialFrame imms a input) evm
      (.assign .localVar ⟨"sqrtRatioNextX96", []⟩ (.var "sqrtRatioTargetX96"))
      (.ok (swapStepPriceFrame imms a input) evm) := by
  simp only [swapStepPriceFrame, swapStepPrice, hr, if_true]
  exact ExecStmt.assign (evalExpr_var_get (swapStepInitialGet imms a input).2.1)
    (assignLocalVarBase_frame (swapStepInitialGet imms a input).2.2.2.2.2)

theorem swapStepNextAssign (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (hi : swapStepExactIn a = input) (hr : swapStepReachTarget a = false) :
    ExecStmt config (swapStepPriceCallFrame imms a input) evm
      (.assign .localVar ⟨"sqrtRatioNextX96", []⟩ (.var (swapStepPriceCallName input)))
      (.ok (swapStepPriceFrame imms a input) evm) := by
  have hg : (swapStepPriceCallFrame imms a input).locals.get? "sqrtRatioNextX96" =
      some (.int 0) := by
    have h := (swapStepInitialGet imms a input).2.2.2.2.2
    cases input <;> simpa only [swapStepPriceCallFrame, swapStepPriceCallName,
      Bool.false_eq_true, if_false, if_true,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using h
  simp only [swapStepPriceFrame, swapStepPrice, hr, Bool.false_eq_true, if_false, hi]
  exact ExecStmt.assign (evalExpr_var_get Std.HashMap.getElem?_insert_self)
    (assignLocalVarBase_frame hg)

theorem swapStepPriceChoiceSource (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (hi : swapStepExactIn a = input) (ha : a.Fits)
    (hv : if swapStepReachTarget a then True else nextPriceValid input (swapStepNextArgs a)) :
    ExecStmt config (swapStepInitialFrame imms a input) evm
      ((swapStepPriceBranch input)[if input then 4 else 3]!)
      (.ok (swapStepPriceFrame imms a input) evm) := by
  have hg := evalSwapStepPriceTest imms evm a input hi
  cases hr : swapStepReachTarget a
  · have hn : nextPriceValid input (swapStepNextArgs a) := by
      simpa only [hr, Bool.false_eq_true, if_false] using hv
    have hc := swapStepPriceCallReturns imms evm a input hi ha hn
    have hs := swapStepNextAssign imms evm a input hi hr
    cases input <;> apply ExecStmt.iteFalse (by simpa only [hr] using hg)
    all_goals
      exact ExecBlock.consNormal
        (by simpa only [nextPriceName, swapStepPriceCallArgs, swapStepPriceCallName,
          swapStepChoiceBudgetExpr, Bool.false_eq_true, if_false, if_true] using hc)
        (ExecBlock.consNormal
          (by simpa only [swapStepPriceCallName, Bool.false_eq_true, if_false, if_true] using hs)
          ExecBlock.nil)
  · have hs := swapStepTargetAssign imms evm a input hr
    cases input <;> apply ExecStmt.iteTrue (by simpa only [hr] using hg)
    all_goals exact ExecBlock.consNormal hs ExecBlock.nil

theorem swapStepPriceBranchSource (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (ha : a.Fits) (hv : swapStepPriceValid a) :
    ExecBlock config (swapStepReadyFrame imms a) evm (swapStepPriceBranch (swapStepExactIn a))
      (.ok (swapStepPriceFrame imms a (swapStepExactIn a)) evm) := by
  have hp := swapStepInitialSource imms evm a (swapStepExactIn a) ha hv.1 hv.2.1
  have hc := swapStepPriceChoiceSource imms evm a (swapStepExactIn a) rfl ha hv.2.2
  cases hi : swapStepExactIn a
  all_goals
    simp only [hi] at hp hc
    exact execBlock_append_ok hp (ExecBlock.consNormal hc ExecBlock.nil)

end Benchmarks.UniswapV3.Pool

import Benchmarks.UniswapV3.Pool.SwapStepInitialModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem swapStepInitialPrefix (imms : Store) (evm : EVM.State) (a : SwapStepArgs) (input : Bool)
    (hv : if input then fullMathValid (EVM.wordOfInt a.remaining) (swapStepComplement a)
      (UInt256.ofNat 1000000) else True) :
    ExecBlock config (swapStepReadyFrame imms a) evm
      ((swapStepPriceBranch input).take (if input then 2 else 1))
      (.ok (swapStepInitialZeroFrame imms a input) evm) := by
  cases input
  · exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil
  · exact ExecBlock.consNormal (swapStepBudgetSource imms evm a hv)
      (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil)

theorem swapStepInitialCallSource (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (ha : a.Fits)
    (hv : amountDeltaValid (swapStepDeltaOne a input) (swapStepDeltaArgs a a.target input)) :
    ExecStmt config (swapStepInitialZeroFrame imms a input) evm
      (.internalCall (amountDeltaName (swapStepDeltaOne a input))
        (swapStepDeltaCallArgs a input "sqrtRatioTargetX96") (swapStepInitialCallName a input))
      (.ok (swapStepInitialCallFrame imms a input) evm) := by
  have hg := swapStepInitialZeroGet imms a input
  exact swapStepDeltaCallReturns _ imms evm a a.target input "sqrtRatioTargetX96"
    (swapStepInitialCallName a input) hg.1 hg.2.1 hg.2.2.1
    (swapStepDeltaArgs_fits a a.target input ha ha.2.1) hv

theorem swapStepInitialChosenSource (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) :
    ExecStmt config (swapStepInitialCallFrame imms a input) evm
      (.assign .localVar ⟨swapStepInitialCondName input, []⟩
        (.var (swapStepInitialCallName a input)))
      (.ok (swapStepInitialChosenFrame imms a input) evm) := by
  have hg : (swapStepInitialCallFrame imms a input).locals.get?
      (swapStepInitialCondName input) = some (.int 0) := by
    cases input <;> cases hz : swapStepZeroForOne a <;>
      simp only [swapStepInitialCallFrame, swapStepInitialCallName, hz,
        Bool.false_eq_true, if_false, if_true, swapStepInitialCondName,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    all_goals swap_step_initial_get
  exact ExecStmt.assign (evalExpr_var_get Std.HashMap.getElem?_insert_self)
    (assignLocalVarBase_frame hg)

theorem swapStepInitialChoiceSource (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (ha : a.Fits)
    (hv : amountDeltaValid (swapStepDeltaOne a input) (swapStepDeltaArgs a a.target input)) :
    ExecStmt config (swapStepInitialZeroFrame imms a input) evm
      ((swapStepPriceBranch input)[if input then 2 else 1]!)
      (.ok (swapStepInitialChosenFrame imms a input) evm) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm)
    (swapStepInitialZeroGet imms a input).2.2.2.1
  have hc := swapStepInitialCallSource imms evm a input ha hv
  have hs := swapStepInitialChosenSource imms evm a input
  cases hz : swapStepZeroForOne a
  · cases input <;> apply ExecStmt.iteFalse (by simpa only [hz] using he)
    all_goals
      exact ExecBlock.consNormal
        (by simpa only [swapStepDeltaOne, swapStepDeltaCallArgs, swapStepInitialCallName,
          amountDeltaName, hz, Bool.not_false, Bool.false_eq_true, if_false, if_true] using hc)
        (ExecBlock.consNormal
          (by simpa only [swapStepInitialCondName, swapStepInitialCallName, hz,
            Bool.false_eq_true, if_false, if_true] using hs) ExecBlock.nil)
  · cases input <;> apply ExecStmt.iteTrue (by simpa only [hz] using he)
    all_goals
      exact ExecBlock.consNormal
        (by simpa only [swapStepDeltaOne, swapStepDeltaCallArgs, swapStepInitialCallName,
          amountDeltaName, hz, Bool.not_true, Bool.false_eq_true, if_false, if_true] using hc)
        (ExecBlock.consNormal
          (by simpa only [swapStepInitialCondName, swapStepInitialCallName, hz,
            Bool.false_eq_true, if_false, if_true] using hs) ExecBlock.nil)

theorem swapStepInitialAssignSource (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) :
    ExecStmt config (swapStepInitialChosenFrame imms a input) evm
      (.assign .localVar ⟨swapStepAmountName input, []⟩ (.var (swapStepInitialCondName input)))
      (.ok (swapStepInitialFrame imms a input) evm) := by
  have hg : (swapStepInitialChosenFrame imms a input).locals.get?
      (swapStepAmountName input) = some (.int 0) := by
    cases input <;> cases hz : swapStepZeroForOne a <;>
      simp only [swapStepInitialChosenFrame, swapStepInitialCallFrame,
        swapStepInitialCallName, swapStepInitialCondName, swapStepAmountName, hz,
        Bool.false_eq_true, if_false, if_true,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    all_goals swap_step_initial_get
  exact ExecStmt.assign (evalExpr_var_get Std.HashMap.getElem?_insert_self)
    (assignLocalVarBase_frame hg)

theorem swapStepInitialSource (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (ha : a.Fits)
    (hb : if input then fullMathValid (EVM.wordOfInt a.remaining) (swapStepComplement a)
      (UInt256.ofNat 1000000) else True)
    (hv : amountDeltaValid (swapStepDeltaOne a input) (swapStepDeltaArgs a a.target input)) :
    ExecBlock config (swapStepReadyFrame imms a) evm
      ((swapStepPriceBranch input).take (if input then 4 else 3))
      (.ok (swapStepInitialFrame imms a input) evm) := by
  have hp := swapStepInitialPrefix imms evm a input hb
  have hc := swapStepInitialChoiceSource imms evm a input ha hv
  have hs := swapStepInitialAssignSource imms evm a input
  cases input
  all_goals
    exact execBlock_append_ok hp (ExecBlock.consNormal hc (ExecBlock.consNormal hs ExecBlock.nil))

end Benchmarks.UniswapV3.Pool

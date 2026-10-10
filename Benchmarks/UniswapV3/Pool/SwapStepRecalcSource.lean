import Benchmarks.UniswapV3.Pool.SwapStepRecalcGet

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem swapStepRecalcCallSource (locals imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (hg : SwapStepCalcGet locals a) (ha : a.Fits) (hp : swapStepPriceValid a)
    (hv : amountDeltaValid (swapStepDeltaOne a input)
      (swapStepDeltaArgs a (swapStepPrice a) input)) :
    ExecStmt config (swapStepCalcFrame imms (swapStepRecalcZeroLocals locals a input)) evm
      (.internalCall (amountDeltaName (swapStepDeltaOne a input))
        (swapStepDeltaCallArgs a input "sqrtRatioNextX96") (swapStepRecalcCallName a input))
      (.ok (swapStepCalcFrame imms (swapStepRecalcCallLocals locals a input)) evm) := by
  have hz := swapStepRecalcZeroGet locals a input hg
  exact swapStepDeltaCallReturns _ imms evm a (swapStepPrice a) input "sqrtRatioNextX96"
    (swapStepRecalcCallName a input) hz.current hz.price hz.liquidity
    (swapStepDeltaArgs_fits a _ input ha (swapStepPrice_fits a ha hp)) hv

theorem swapStepRecalcKeepSource (locals imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (hk : swapStepKeep a input = true)
    (hg : locals.get? (swapStepAmountName input) =
      some (.int (Int.ofNat (swapStepBeforeAmount a input).toNat))) :
    ExecStmt config (swapStepCalcFrame imms (swapStepRecalcZeroLocals locals a input)) evm
      (.assign .localVar ⟨swapStepRecalcCondName a input, []⟩ (.var (swapStepAmountName input)))
      (.ok (swapStepCalcFrame imms (swapStepRecalcChosenLocals locals a input)) evm) := by
  have ho : (swapStepRecalcZeroLocals locals a input).get? (swapStepAmountName input) =
      some (.int (Int.ofNat (swapStepBeforeAmount a input).toNat)) := by
    rw [swapStepRecalcZeroGet_other _ _ _ _ (by swap_step_recalc_name)]
    exact hg
  simp only [swapStepRecalcChosenLocals, swapStepAmount, hk, if_true]
  exact ExecStmt.assign (evalExpr_var_get ho)
    (assignLocalVarBase_frame Std.HashMap.getElem?_insert_self)

theorem swapStepRecalcCallAssign (locals imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (hk : swapStepKeep a input = false) :
    ExecStmt config (swapStepCalcFrame imms (swapStepRecalcCallLocals locals a input)) evm
      (.assign .localVar ⟨swapStepRecalcCondName a input, []⟩
        (.var (swapStepRecalcCallName a input)))
      (.ok (swapStepCalcFrame imms (swapStepRecalcChosenLocals locals a input)) evm) := by
  have hn : (swapStepRecalcCallName a input == swapStepRecalcCondName a input) = false := by
    swap_step_recalc_name
  have hg : (swapStepRecalcCallLocals locals a input).get? (swapStepRecalcCondName a input) =
      some (.int 0) := by
    simp only [swapStepRecalcCallLocals, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, hn, Bool.false_eq_true, if_false]
    exact Std.HashMap.getElem?_insert_self
  simp only [swapStepRecalcChosenLocals, swapStepAmount, hk, Bool.false_eq_true, if_false]
  exact ExecStmt.assign (evalExpr_var_get Std.HashMap.getElem?_insert_self)
    (assignLocalVarBase_frame hg)

theorem swapStepRecalcAssign (locals imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool)
    (hg : locals.get? (swapStepAmountName input) =
      some (.int (Int.ofNat (swapStepBeforeAmount a input).toNat))) :
    ExecStmt config (swapStepCalcFrame imms (swapStepRecalcChosenLocals locals a input)) evm
      (.assign .localVar ⟨swapStepAmountName input, []⟩ (.var (swapStepRecalcCondName a input)))
      (.ok (swapStepCalcFrame imms (swapStepRecalcLocals locals a input)) evm) := by
  have hc : (swapStepRecalcCondName a input == swapStepAmountName input) = false := by
    swap_step_recalc_name
  have hr : (swapStepRecalcCallName a input == swapStepAmountName input) = false := by
    swap_step_recalc_name
  have ho : (swapStepRecalcChosenLocals locals a input).get? (swapStepAmountName input) =
      some (.int (Int.ofNat (swapStepBeforeAmount a input).toNat)) := by
    cases hk : swapStepKeep a input <;>
      simpa only [swapStepRecalcChosenLocals, swapStepRecalcCallLocals,
        swapStepRecalcZeroLocals, hk, Bool.false_eq_true, if_false, if_true,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hc, hr] using hg
  exact ExecStmt.assign (evalExpr_var_get Std.HashMap.getElem?_insert_self)
    (assignLocalVarBase_frame ho)

theorem swapStepRecalcChoiceSource (locals imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (hg : SwapStepCalcGet locals a) (ha : a.Fits) (hp : swapStepPriceValid a)
    (hv : swapStepRecalcValid a input)
    (ho : locals.get? (swapStepAmountName input) =
      some (.int (Int.ofNat (swapStepBeforeAmount a input).toNat))) :
    ExecStmt config (swapStepCalcFrame imms (swapStepRecalcZeroLocals locals a input)) evm
      (swapStepRecalcBlock a input)[1]!
      (.ok (swapStepCalcFrame imms (swapStepRecalcChosenLocals locals a input)) evm) := by
  have he := evalSwapStepRecalcTest
    (swapStepCalcFrame imms (swapStepRecalcZeroLocals locals a input)) evm a input
    (swapStepRecalcZeroGet locals a input hg)
  cases hk : swapStepKeep a input
  · have hd : amountDeltaValid (swapStepDeltaOne a input)
        (swapStepDeltaArgs a (swapStepPrice a) input) := by
      simpa only [swapStepRecalcValid, hk, Bool.false_eq_true, if_false] using hv
    exact ExecStmt.iteFalse (by simpa only [hk] using he)
      (ExecBlock.consNormal (swapStepRecalcCallSource locals imms evm a input hg ha hp hd)
        (ExecBlock.consNormal (swapStepRecalcCallAssign locals imms evm a input hk) ExecBlock.nil))
  · exact ExecStmt.iteTrue (by simpa only [hk] using he)
      (ExecBlock.consNormal (swapStepRecalcKeepSource locals imms evm a input hk ho) ExecBlock.nil)

theorem swapStepRecalcSource (locals imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (hg : SwapStepCalcGet locals a) (ha : a.Fits) (hp : swapStepPriceValid a)
    (hv : swapStepRecalcValid a input)
    (ho : locals.get? (swapStepAmountName input) =
      some (.int (Int.ofNat (swapStepBeforeAmount a input).toNat))) :
    ExecBlock config (swapStepCalcFrame imms locals) evm (swapStepRecalcBlock a input)
      (.ok (swapStepCalcFrame imms (swapStepRecalcLocals locals a input)) evm) := by
  refine ExecBlock.consNormal
    (solm' := swapStepCalcFrame imms (swapStepRecalcZeroLocals locals a input))
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  exact ExecBlock.consNormal (swapStepRecalcChoiceSource locals imms evm a input hg ha hp hv ho)
    (ExecBlock.consNormal (swapStepRecalcAssign locals imms evm a input ho) ExecBlock.nil)

end Benchmarks.UniswapV3.Pool

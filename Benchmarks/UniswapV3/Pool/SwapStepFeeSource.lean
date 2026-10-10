import Benchmarks.UniswapV3.Pool.SwapStepFeeCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem swapStepUnusedFeeAssign (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (hu : swapStepUnusedFee a = true) :
    ExecStmt config (swapStepCapFrame imms a) evm
      (.assign .localVar ⟨"feeAmount", []⟩
        (.cast (.binary .sub
          (.cast (.var "amountRemaining") (.elem (.int (.uint ⟨256, by decide⟩))))
          (.var "amountIn")) (.elem (.int (.uint ⟨256, by decide⟩)))))
      (.ok (swapStepResultFrame imms a) evm) := by
  simp only [swapStepResultFrame, swapStepFee, hu, if_true]
  exact ExecStmt.assign
    (evalExpr_word_sub (evalSwapStepRemainingWord _ evm a (swapStepCapExtraGet imms a).1)
      (evalExpr_var_get (swapStepCapAmountsGet imms a).1))
    (assignLocalVarBase_frame (swapStepCapExtraGet imms a).2.2.2)

theorem swapStepFeeCallAssign (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (hu : swapStepUnusedFee a = false) :
    ExecStmt config (swapStepFeeCallFrame imms a) evm
      (.assign .localVar ⟨"feeAmount", []⟩ (.var "__c17"))
      (.ok (swapStepResultFrame imms a) evm) := by
  have hg : (swapStepFeeCallFrame imms a).locals.get? "feeAmount" = some (.int 0) := by
    simpa only [swapStepFeeCallFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using (swapStepCapExtraGet imms a).2.2.2
  simp only [swapStepResultFrame, swapStepFee, hu, Bool.false_eq_true, if_false]
  exact ExecStmt.assign (evalExpr_var_get Std.HashMap.getElem?_insert_self)
    (assignLocalVarBase_frame hg)

theorem swapStepFeeSource (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (hv : swapStepFeeValid a) :
    ExecStmt config (swapStepCapFrame imms a) evm swapStepFunction.body[10]!
      (.ok (swapStepResultFrame imms a) evm) := by
  have he := evalSwapStepFeeTest imms evm a
  cases hu : swapStepUnusedFee a
  · have hf : fullMathRoundValid (swapStepAmount a true) a.fee (swapStepComplement a) := by
      simpa only [swapStepFeeValid, hu, Bool.false_eq_true, if_false] using hv
    exact ExecStmt.iteFalse (by simpa only [hu] using he)
      (ExecBlock.consNormal (swapStepFeeCallReturns imms evm a hf)
        (ExecBlock.consNormal (swapStepFeeCallAssign imms evm a hu) ExecBlock.nil))
  · exact ExecStmt.iteTrue (by simpa only [hu] using he)
      (ExecBlock.consNormal (swapStepUnusedFeeAssign imms evm a hu) ExecBlock.nil)

theorem swapStepFeeReverts (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (hv : ¬swapStepFeeValid a) :
    ExecStmt config (swapStepCapFrame imms a) evm swapStepFunction.body[10]! .reverted := by
  have hu : swapStepUnusedFee a = false := by
    cases h : swapStepUnusedFee a
    · rfl
    · exact False.elim (hv (by simp only [swapStepFeeValid, h, if_true]))
  have hf : ¬fullMathRoundValid (swapStepAmount a true) a.fee (swapStepComplement a) := by
    simpa only [swapStepFeeValid, hu, Bool.false_eq_true, if_false] using hv
  exact ExecStmt.iteFalse (by simpa only [hu] using evalSwapStepFeeTest imms evm a)
    (ExecBlock.consRevert (swapStepFeeCallReverts imms evm a hf))

end Benchmarks.UniswapV3.Pool

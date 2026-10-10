import Benchmarks.UniswapV3.Pool.SwapStepPriceChoice
import Benchmarks.UniswapV3.Pool.SwapStepInitialReverts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem swapStepPriceStmtSource (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (ha : a.Fits) (hv : swapStepPriceValid a) :
    ExecStmt config (swapStepReadyFrame imms a) evm swapStepFunction.body[6]!
      (.ok (swapStepPriceFrame imms a (swapStepExactIn a)) evm) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm)
    (swapStepReadyGet imms a).2.2.2.2.2.2
  have hb := swapStepPriceBranchSource imms evm a ha hv
  cases hi : swapStepExactIn a
  · exact ExecStmt.iteFalse (by simpa only [hi] using he) (by simpa only [hi] using hb)
  · exact ExecStmt.iteTrue (by simpa only [hi] using he) (by simpa only [hi] using hb)

theorem swapStepPriceSource (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (ha : a.Fits) (hv : swapStepPriceValid a) :
    ExecBlock config (swapStepFrame imms a) evm (swapStepFunction.body.take 7)
      (.ok (swapStepPriceFrame imms a (swapStepExactIn a)) evm) := by
  exact execBlock_append_ok (swapStepPrefixSource imms evm a)
    (ExecBlock.consNormal (swapStepPriceStmtSource imms evm a ha hv) ExecBlock.nil)

theorem swapStepPriceChoiceReverts (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (hi : swapStepExactIn a = input) (hr : swapStepReachTarget a = false)
    (hv : ¬nextPriceValid input (swapStepNextArgs a)) :
    ExecStmt config (swapStepInitialFrame imms a input) evm
      ((swapStepPriceBranch input)[if input then 4 else 3]!) .reverted := by
  have he := evalSwapStepPriceTest imms evm a input hi
  have hc := swapStepPriceCallReverts imms evm a input hi hv
  cases input <;> apply ExecStmt.iteFalse (by simpa only [hr] using he)
  all_goals
    apply ExecBlock.consRevert
    simpa only [nextPriceName, swapStepPriceCallArgs, swapStepPriceCallName,
      swapStepChoiceBudgetExpr, Bool.false_eq_true, if_false, if_true] using hc

theorem swapStepPriceReverts (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (ha : a.Fits) (hv : ¬swapStepPriceValid a) :
    ExecFuncBody config (swapStepFrame imms a) evm swapStepFunction.body .reverted := by
  classical
  by_cases hb : swapStepBudgetValid a
  · by_cases hd : swapStepInitialValid a
    · have hn : ¬(if swapStepReachTarget a then True
          else nextPriceValid (swapStepExactIn a) (swapStepNextArgs a)) :=
        fun h ↦ hv ⟨hb, hd, h⟩
      have hr : swapStepReachTarget a = false := by
        cases h : swapStepReachTarget a
        · rfl
        · exact False.elim (hn (by simp only [h, if_true]))
      simp only [hr, Bool.false_eq_true, if_false] at hn
      have hp := swapStepInitialSource imms evm a (swapStepExactIn a) ha hb hd
      have hc := swapStepPriceChoiceReverts imms evm a (swapStepExactIn a) rfl hr hn
      have he := evalExpr_var_get (cfg := config) (evm := evm)
        (swapStepReadyGet imms a).2.2.2.2.2.2
      apply ExecFuncBody.execBlockRevert
      rw [← List.take_append_drop 6 swapStepFunction.body]
      apply execBlock_append_ok (swapStepPrefixSource imms evm a)
      apply ExecBlock.consRevert
      cases hi : swapStepExactIn a
      · apply ExecStmt.iteFalse (by simpa only [hi] using he)
        simp only [hi] at hp hc
        exact execBlock_append_ok hp (ExecBlock.consRevert hc)
      · apply ExecStmt.iteTrue (by simpa only [hi] using he)
        simp only [hi] at hp hc
        exact execBlock_append_ok hp (ExecBlock.consRevert hc)
    · exact swapStepInitialFunctionReverts imms evm a ha hb hd
  · exact swapStepBudgetFunctionReverts imms evm a hb

end Benchmarks.UniswapV3.Pool

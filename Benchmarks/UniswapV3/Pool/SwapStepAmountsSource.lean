import Benchmarks.UniswapV3.Pool.SwapStepMaxSource
import Benchmarks.UniswapV3.Pool.SwapStepRecalcSource
import Benchmarks.UniswapV3.Pool.SwapStepRecalcReverts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

noncomputable def swapStepAmountsValid (a : SwapStepArgs) : Prop :=
  swapStepPriceValid a ∧ swapStepRecalcValid a true ∧ swapStepRecalcValid a false

theorem swapStepAmountInGet (imms : Store) (a : SwapStepArgs) :
    SwapStepCalcGet (swapStepAmountInFrame imms a).locals a :=
  swapStepRecalcGet _ a true (swapStepMaxGet imms a)

theorem swapStepAmountInOutputGet (imms : Store) (a : SwapStepArgs) :
    (swapStepAmountInFrame imms a).locals.get? "amountOut" =
      some (.int (Int.ofNat (swapStepBeforeAmount a false).toNat)) := by
  change (swapStepRecalcLocals _ a true).get? "amountOut" = _
  rw [swapStepRecalcGet_other _ _ _ _ (by swap_step_recalc_name)
    (by swap_step_recalc_name) rfl]
  exact swapStepMaxAmountGet imms a false

theorem swapStepAmountsGet (imms : Store) (a : SwapStepArgs) :
    SwapStepCalcGet (swapStepAmountsFrame imms a).locals a :=
  swapStepRecalcGet _ a false (swapStepAmountInGet imms a)

theorem swapStepAmountsAmountGet (imms : Store) (a : SwapStepArgs) :
    (swapStepAmountsFrame imms a).locals.get? "amountIn" =
      some (.int (Int.ofNat (swapStepAmount a true).toNat)) ∧
    (swapStepAmountsFrame imms a).locals.get? "amountOut" =
      some (.int (Int.ofNat (swapStepAmount a false).toNat)) := by
  constructor
  · change (swapStepRecalcLocals _ a false).get? "amountIn" = _
    rw [swapStepRecalcGet_other _ _ _ _ (by swap_step_recalc_name)
      (by swap_step_recalc_name) rfl]
    exact Std.HashMap.getElem?_insert_self
  · exact Std.HashMap.getElem?_insert_self

theorem swapStepAmountsBranchSource (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (ha : a.Fits) (hv : swapStepAmountsValid a) :
    ExecBlock config (swapStepMaxFrame imms a) evm
      (swapStepRecalcBranch (swapStepZeroForOne a)) (.ok (swapStepAmountsFrame imms a) evm) := by
  rw [swapStepRecalcBlock_eq]
  exact execBlock_append_ok
    (swapStepRecalcSource _ imms evm a true (swapStepMaxGet imms a) ha hv.1 hv.2.1
      (swapStepMaxAmountGet imms a true))
    (swapStepRecalcSource _ imms evm a false (swapStepAmountInGet imms a) ha hv.1 hv.2.2
      (swapStepAmountInOutputGet imms a))

theorem swapStepAmountsStmt (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (result : ExecResult)
    (hb : ExecBlock config (swapStepMaxFrame imms a) evm
      (swapStepRecalcBranch (swapStepZeroForOne a)) result) :
    ExecStmt config (swapStepMaxFrame imms a) evm swapStepFunction.body[8]! result := by
  have hg : (swapStepMaxFrame imms a).locals.get? "zeroForOne" =
      some (.bool (swapStepZeroForOne a)) := by
    simp only [swapStepMaxFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rw [← Std.HashMap.get?_eq_getElem?, swapStepPriceGet_other imms a _ _ rfl rfl rfl]
    exact (swapStepInitialGet imms a _).2.2.2.2.1
  have he := evalExpr_var_get (cfg := config) (evm := evm) hg
  cases hz : swapStepZeroForOne a
  · exact ExecStmt.iteFalse (by simpa only [hz] using he) (by simpa only [hz] using hb)
  · exact ExecStmt.iteTrue (by simpa only [hz] using he) (by simpa only [hz] using hb)

theorem swapStepAmountsSource (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (ha : a.Fits) (hv : swapStepAmountsValid a) :
    ExecBlock config (swapStepFrame imms a) evm (swapStepFunction.body.take 9)
      (.ok (swapStepAmountsFrame imms a) evm) :=
  execBlock_append_ok (swapStepMaxPrefixSource imms evm a ha hv.1)
    (ExecBlock.consNormal (swapStepAmountsStmt imms evm a _
      (swapStepAmountsBranchSource imms evm a ha hv)) ExecBlock.nil)

theorem swapStepAmountsReverts (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (ha : a.Fits) (hv : ¬swapStepAmountsValid a) :
    ExecFuncBody config (swapStepFrame imms a) evm swapStepFunction.body .reverted := by
  classical
  by_cases hp : swapStepPriceValid a
  · have hb : ExecBlock config (swapStepMaxFrame imms a) evm
        (swapStepRecalcBranch (swapStepZeroForOne a)) .reverted := by
      rw [swapStepRecalcBlock_eq]
      by_cases hi : swapStepRecalcValid a true
      · exact execBlock_append_ok
          (swapStepRecalcSource _ imms evm a true (swapStepMaxGet imms a) ha hp hi
            (swapStepMaxAmountGet imms a true))
          (swapStepRecalcReverts _ imms evm a false (swapStepAmountInGet imms a) ha hp
            (fun h ↦ hv ⟨hp, hi, h⟩))
      · exact execBlock_append_term
          (swapStepRecalcReverts _ imms evm a true (swapStepMaxGet imms a) ha hp hi)
          (by intros; exact ExecResult.noConfusion)
    apply ExecFuncBody.execBlockRevert
    rw [← List.take_append_drop 8 swapStepFunction.body]
    exact execBlock_append_ok (swapStepMaxPrefixSource imms evm a ha hp)
      (ExecBlock.consRevert (swapStepAmountsStmt imms evm a _ hb))
  · exact swapStepPriceReverts imms evm a ha hp

end Benchmarks.UniswapV3.Pool

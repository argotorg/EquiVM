import Benchmarks.UniswapV3.Pool.TickUpdateInitializeSource

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem tickUpdateStatic (imms : Store) (evm : EVM.State) (a : TickUpdateArgs)
    (hv : liquidityDeltaValid (tickUpdateGrossBefore a evm) a.delta)
    (hm : tickUpdateGrossAfter a evm ≤ Int.ofNat a.maxLiquidity.toNat)
    (hp : evm.executionEnv.perm = false) :
    ExecFuncBody fork config (tickUpdateFrame imms a) evm tickUpdateFunction.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  rw [← List.take_append_drop 6 tickUpdateFunction.body]
  apply execBlock_append_ok (tickUpdateCheckedSource imms evm a hv hm)
  have hc := evalTickUpdateInitConditions imms evm a
  by_cases hz : tickUpdateGrossBefore a evm = 0
  · apply ExecBlock.consStatic
    apply ExecStmt.iteTrue (by simpa only [hz, decide_true] using hc.1)
    by_cases ht : a.tick ≤ a.current
    · apply ExecBlock.consStatic
      apply ExecStmt.iteTrue (by simpa only [ht, decide_true] using hc.2)
      apply ExecBlock.consStatic
      apply execStmt_assign_static (slot := ⟨"info", [.field "feeGrowthOutside0X128"]⟩)
        (rhs := .var "feeGrowthGlobal0X128")
        (stele' := tickUpdateFlippedFrame imms a evm)
        (evm' := tickFeeOutsideState evm a.tick false a.global0) ?_ hp
      exact execStmt_assign_storage (evalExpr_var_get (name := "feeGrowthGlobal0X128")
        (by tick_update_get))
        (assignTickFeeOutside (tickUpdateFlippedFrame imms a evm).locals imms evm "info"
          a.tick false a.global0 (by tick_update_get))
    · refine ExecBlock.consNormal (ExecStmt.iteFalse
        (by simpa only [ht, decide_false] using hc.2) ExecBlock.nil) ?_
      apply ExecBlock.consStatic
      apply execStmt_assign_static (slot := ⟨"info", [.field "initialized"]⟩)
        (stele' := tickUpdateFlippedFrame imms a evm)
        (rhs := .boolLit true) (evm' := tickHistoryState evm a.tick .initialized ⟨1⟩) ?_ hp
      exact execStmt_assign_storage (rhs := .boolLit true) (by simp only [evalExpr?, pure])
        (assignTickHistory (tickUpdateFlippedFrame imms a evm).locals imms evm "info" a.tick
          .initialized (.bool true) ⟨1⟩ (by tick_update_get) rfl)
  · have hskip : ExecStmt fork config (tickUpdateFlippedFrame imms a evm) evm
        (tickUpdateFunction.body[6]!)
        (.ok (tickUpdateFlippedFrame imms a evm) (tickUpdateInitializedState a evm)) := by
      simp only [tickUpdateInitializedState, if_neg hz]
      exact ExecStmt.iteFalse (by simpa only [hz, decide_false] using hc.1) ExecBlock.nil
    refine ExecBlock.consNormal hskip ?_
    exact ExecBlock.consStatic (execStmt_assign_static (tickUpdateGrossSource imms evm a)
      (by rw [tickUpdateInitializedState_executionEnv]; exact hp))

end Benchmarks.UniswapV3.Pool

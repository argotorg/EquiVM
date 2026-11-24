import Benchmarks.UniswapV3.Pool.TickCrossModel

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

macro "tick_cross_get" : tactic => `(tactic| (
  simp only [tickCrossResultFrame, tickCrossAliasFrame, tickCrossZeroFrame,
    tickCrossFrame, tickCrossLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  rfl))

theorem tickCrossPrefix (imms : Store) (evm : EVM.State) (a : TickCrossArgs) :
    ExecBlock fork config (tickCrossFrame imms a) evm (tickCrossFunction.body.take 2)
      (.ok (tickCrossAliasFrame imms a) evm) := by
  refine ExecBlock.consNormal (stele' := tickCrossZeroFrame imms a)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage ?_) ExecBlock.nil
  apply resolveTickReference _ imms evm "tick" a.tick
  · simp [tickCrossLocals]
  · tick_cross_get

def tickCrossFeeExpr (second : Bool) : Expr :=
  .cast (.binary .sub (.var (tickFeeGlobalName second))
    (.storage ⟨"info", [.field (tickFeeOutsideName second)]⟩))
    (.elem (.int (.uint ⟨256, by decide⟩)))

theorem tickCrossFeeSource (imms : Store) (evm : EVM.State) (a : TickCrossArgs)
    (second : Bool) :
    ExecStmt fork config (tickCrossAliasFrame imms a) evm
      (.assign .storage ⟨"info", [.field (tickFeeOutsideName second)]⟩ (tickCrossFeeExpr second))
      (if evm.executionEnv.perm then .ok (tickCrossAliasFrame imms a)
        (tickCrossFeeState evm a second) else .staticViolation) := by
  apply execStmt_assign_storage (value := .int
    (Int.ofNat (tickCrossFeeWord a second evm.accountMap evm.executionEnv).toNat))
  · apply evalExpr_word_sub
    · apply evalExpr_var_get
      cases second <;> tick_cross_get
    · exact evalTickAliasFeeGrowth (tickCrossAliasFrame imms a).locals imms evm
        "info" a.tick second (by tick_cross_get)
  · exact assignTickFeeOutside (tickCrossAliasFrame imms a).locals imms evm "info" a.tick
      second _ (by tick_cross_get)

theorem tickCrossFeesSource (imms : Store) (evm : EVM.State) (a : TickCrossArgs)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config (tickCrossFrame imms a) evm (tickCrossFunction.body.take 4)
      (.ok (tickCrossAliasFrame imms a)
        (tickCrossFeeState (tickCrossFeeState evm a false) a true)) :=
  execBlock_append_ok (tickCrossPrefix imms evm a)
    (ExecBlock.consNormal (by simpa only [hperm, if_true] using tickCrossFeeSource imms evm a false)
      (ExecBlock.consNormal (by simpa only [tickCrossFeeState, tickFeeOutsideState_executionEnv, hperm, if_true] using (tickCrossFeeSource imms (tickCrossFeeState evm a false) a true)) ExecBlock.nil))

theorem tickCrossStatic (imms : Store) (evm : EVM.State) (a : TickCrossArgs)
    (hp : evm.executionEnv.perm = false) :
    ExecFuncBody fork config (tickCrossFrame imms a) evm tickCrossFunction.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  rw [← List.take_append_drop 2 tickCrossFunction.body]
  apply execBlock_append_ok (tickCrossPrefix imms evm a)
  apply ExecBlock.consStatic
  exact execStmt_assign_static (tickCrossFeeSource imms evm a false) hp

end Benchmarks.UniswapV3.Pool

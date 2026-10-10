import Benchmarks.UniswapV3.Pool.TickCrossPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def tickCrossHistoryExpr (field : TickCrossField) : Expr :=
  .cast (.binary .sub (.var field.globalName)
    (.storage ⟨"info", [.field field.field.name]⟩)) (.elem (.int field.type))

theorem evalTickCrossHistoryOld (imms : Store) (evm : EVM.State) (a : TickCrossArgs)
    (field : TickCrossField) :
    evalExpr? config (tickCrossAliasFrame imms a) evm
      (.storage ⟨"info", [.field field.field.name]⟩) =
      .ok (.int (field.old (solcSlotWordAt (tickFieldSlot a.tick 3)
        evm.accountMap evm.executionEnv))) := by
  cases field with
  | secondsPerLiquidity =>
    exact evalTickAliasSecondsPerLiquidity (tickCrossAliasFrame imms a).locals imms evm
      "info" a.tick (by tick_cross_get)
  | cumulative =>
    have h := evalTickAliasCumulative (tickCrossAliasFrame imms a).locals imms evm
      "info" a.tick (by tick_cross_get)
    simpa only [tickSignedFieldValue, Nat.pow_zero,
      show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl, word_div_one] using h
  | seconds =>
    exact evalTickAliasSeconds (tickCrossAliasFrame imms a).locals imms evm
      "info" a.tick (by tick_cross_get)

theorem evalTickCrossHistory (imms : Store) (evm : EVM.State) (a : TickCrossArgs)
    (field : TickCrossField) :
    evalExpr? config (tickCrossAliasFrame imms a) evm (tickCrossHistoryExpr field) =
      .ok (.int (tickCrossHistoryValue a field
        (solcSlotWordAt (tickFieldSlot a.tick 3) evm.accountMap evm.executionEnv))) := by
  have hg : evalExpr? config (tickCrossAliasFrame imms a) evm (.var field.globalName) =
      .ok (.int (field.global a)) := by
    apply evalExpr_var_get
    cases field <;> tick_cross_get
  have ho := evalTickCrossHistoryOld imms evm a field
  apply evalExpr_intCast
  simp only [evalExpr?, hg, ho, evalBinaryOp?, bind, EvalResult.bind]

theorem tickCrossHistorySource (imms : Store) (evm : EVM.State) (a : TickCrossArgs)
    (field : TickCrossField) :
    ExecStmt config (tickCrossAliasFrame imms a) evm
      (.assign .storage ⟨"info", [.field field.field.name]⟩ (tickCrossHistoryExpr field))
      (.ok (tickCrossAliasFrame imms a) (tickCrossHistoryState evm a field)) := by
  refine ExecStmt.assign (evalTickCrossHistory imms evm a field) ?_
  have h := assignTickHistory (tickCrossAliasFrame imms a).locals imms evm "info" a.tick
    field.field (.int (tickCrossHistoryValue a field
      (solcSlotWordAt (tickFieldSlot a.tick 3) evm.accountMap evm.executionEnv))) _
    (by tick_cross_get) rfl
  convert h using 1

theorem tickCrossStoresSource (imms : Store) (evm : EVM.State) (a : TickCrossArgs) :
    ExecBlock config (tickCrossFrame imms a) evm (tickCrossFunction.body.take 7)
      (.ok (tickCrossAliasFrame imms a) (tickCrossState evm a)) := by
  exact execBlock_append_ok (tickCrossFeesSource imms evm a)
    (ExecBlock.consNormal (tickCrossHistorySource imms _ a .secondsPerLiquidity)
      (ExecBlock.consNormal (tickCrossHistorySource imms _ a .cumulative)
        (ExecBlock.consNormal (tickCrossHistorySource imms _ a .seconds) ExecBlock.nil)))

end Benchmarks.UniswapV3.Pool

import Benchmarks.UniswapV3.Pool.TickClearStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def tickClearFunction : FunctionDecl := contract.functions[46]!

theorem tickClearLookup : lookupCallable? contract "Tick_clear" =
    some tickClearFunction.toCallable := rfl

def tickClearLocals (tick : Int) : Store := (∅ : Store).insert "tick" (.int tick)

def tickClearFrame (imms : Store) (tick : Int) : Frame :=
  {contract := contract, locals := tickClearLocals tick, immutables := imms}

theorem tickClearBind (tick : Int) :
    bindParams? tickClearFunction.params [.int tick] = some (tickClearLocals tick) := rfl

theorem deleteTick (imms : Store) (evm : EVM.State) (tick : Int) :
    deleteStorage? config (tickClearFrame imms tick) evm ⟨"ticks", [.mindex (.var "tick")]⟩ =
      .ok (tickClearState evm tick) := by
  have hr := resolveTickReference (tickClearLocals tick) imms evm "tick" tick
    (by simp [tickClearLocals]) (by simp [tickClearLocals, Std.HashMap.getElem_insert])
  change resolveStorageRef? config (tickClearFrame imms tick) evm _ = _ at hr
  simp only [deleteStorage?, usesTransientStorage_of_resolveStorageRef hr,
    Bool.false_eq_true, if_false, hr, EvalResult.bind, bind]
  exact tickClearStorage evm tick

theorem tickClearReturns (imms : Store) (evm : EVM.State) (tick : Int) :
    ExecFuncBody config (tickClearFrame imms tick) evm tickClearFunction.body
      (.returned (tickClearFrame imms tick) (tickClearState evm tick) none) := by
  apply ExecFuncBody.execBlockOK
  exact ExecBlock.consNormal (ExecStmt.delete (deleteTick imms evm tick)) ExecBlock.nil

theorem tickClearStatic (imms : Store) (evm : EVM.State) (tick : Int)
    (hp : evm.executionEnv.perm = false) :
    ExecFuncBody config (tickClearFrame imms tick) evm tickClearFunction.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  exact ExecBlock.consStatic (ExecStmt.deleteStatic (deleteTick imms evm tick) hp)

end Benchmarks.UniswapV3.Pool

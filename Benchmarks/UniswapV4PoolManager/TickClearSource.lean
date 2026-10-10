import Benchmarks.UniswapV4PoolManager.TickStorage
import Benchmarks.UniswapV4PoolManager.CallComposition
import Reasoning.PackedStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickClearPost (evm : EVM.State) (id : UInt256) (tick : Int) : EVM.State :=
  let e0 := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (tickSlot id tick) ⟨0⟩
  let e1 := Solm.EVM.storageStore e0 e0.executionEnv.codeOwner (tickSlot id tick+⟨1⟩) ⟨0⟩
  Solm.EVM.storageStore e1 e1.executionEnv.codeOwner (tickSlot id tick+⟨2⟩) ⟨0⟩

theorem tickClearStorage {f : Frame} {evm : EVM.State} {id : UInt256} {tick : Int}
    (hs : f.locals.get? "self" = some (poolRefValue id))
    (ht : f.locals.get? "tick" = some (.int tick)) :
    deleteStorage? config f evm {base := "self", steps := [.field "ticks", .mindex (.var "tick")]} =
      .ok (tickClearPost evm id tick) := by
  have hr := tickMappingResolve (f := f) (evm := evm) hs (evalLocalValue ht)
  simp only [deleteStorage?, usesTransientStorage_of_resolveStorageRef hr,
    Bool.false_eq_true, if_false, hr, bind, EvalResult.bind]
  change solidityClearStorage? config.storageBackend.locate? evm (tickRef id tick) tickInfoType = _
  have hclear (e : EVM.State) (field : TickField) :
      solidityClearStorage? config.storageBackend.locate? e
        {tickRef id tick with steps := (tickRef id tick).steps ++ [.field field.name]}
        (.elem (.int (.uint ⟨256, by decide⟩))) =
          .ok (Solm.EVM.storageStore e e.executionEnv.codeOwner (field.slot (tickSlot id tick)) ⟨0⟩) :=
    clearStorage_uint256_zero (tickField_loc id tick field)
  change solidityClearStorage? config.storageBackend.locate? evm (tickRef id tick)
    (.struct "TickInfo" [("liquidityPacked", .elem (.int (.uint ⟨256, by decide⟩))),
      ("feeGrowthOutside0X128", .elem (.int (.uint ⟨256, by decide⟩))),
      ("feeGrowthOutside1X128", .elem (.int (.uint ⟨256, by decide⟩)))]) = _
  have h0 := hclear evm .liquidityPacked
  have h1 (e : EVM.State) := hclear e .feeGrowthOutside0
  have h2 (e : EVM.State) := hclear e .feeGrowthOutside1
  dsimp only [TickField.name, TickField.slot] at h0 h1 h2
  rw [solidityClearStorage?, solidityClearFields?, h0]
  simp only [bind, EvalResult.bind]
  rw [solidityClearFields?, h1]
  simp only [bind, EvalResult.bind]
  rw [solidityClearFields?, h2]
  simp only [bind, EvalResult.bind, solidityClearFields?]
  rfl

abbrev tickClearFunction : FunctionDecl := contract.functions[68]!
theorem tickClear_lookup : lookupCallable? contract "Pool_clearTick" = some tickClearFunction.toCallable := rfl
def tickClearResult (f : Frame) (evm : EVM.State) (id : UInt256) (tick : Int) : ExecResult :=
  if evm.executionEnv.perm = false then .staticViolation else .returned f (tickClearPost evm id tick) none

theorem tickClearBody {f : Frame} {evm : EVM.State} {id : UInt256} {tick : Int}
    (hs : f.locals.get? "self" = some (poolRefValue id))
    (ht : f.locals.get? "tick" = some (.int tick)) :
    ExecFuncBody config f evm tickClearFunction.body (tickClearResult f evm id tick) := by
  have hc := tickClearStorage (evm := evm) hs ht
  unfold tickClearResult
  by_cases hp : evm.executionEnv.perm = false
  · rw [if_pos hp]
    exact .execBlockStatic (ExecBlock.consStatic (ExecStmt.deleteStatic hc hp))
  · rw [if_neg hp]
    exact .execBlockOK (execBlock_singleton (ExecStmt.delete hc))

theorem tickClearCall {f : Frame} {evm : EVM.State} {es et : Expr} {id : UInt256} {tick : Int}
    (hf : f.contract = contract) (hs : evalExpr? config f evm es = .ok (poolRefValue id))
    (ht : evalExpr? config f evm et = .ok (.int tick)) (ret : Ident) :
    ExecStmt config f evm (.internalCall "Pool_clearTick" [es, et] ret)
      (resumeCallResult f ret (tickClearResult f evm id tick)) := by
  have hb := tickClearBody (evm := evm)
    (f := {f with locals := (((∅ : Store).insert "tick" (.int tick)).insert "self" (poolRefValue id))})
    (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("self" == "tick") = false)).trans (store_get_self _ _ _))
  have hc := internalCallFunctionExec (caller := f) (name := "Pool_clearTick") (retVar := ret)
    (args := [es, et]) (argVals := [poolRefValue id, .int tick])
    (by simp only [evalExprs?, hs, ht, bind, EvalResult.bind, pure])
    (by rw [hf]; exact tickClear_lookup) rfl hb
  simpa only [tickClearResult, resumeCallResult_ite, resumeCallResult_returned, resumeCallResult_static] using hc

end Benchmarks.UniswapV4PoolManager

import Benchmarks.Morpho.MetaMorphoV1_1.SupplyQueueStorageSource

/-! Source outcomes for replacement of the supply queue. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

theorem supplyQueueForInit (frame : Frame) (evm : State) :
    ExecBlock config frame evm [.letDecl "i" (some abiUInt256) (.intLit 0)]
      (.ok (supplyQueueIndexFrame frame 0) evm) :=
  ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0)
    (by simp only [evalExpr?, pure])) ExecBlock.nil

theorem supplyQueueGuardPrefix (evm : State) (imms : Store) (values : List Value)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hrole : allocatorRoleAllowed evm)
    (hlen : values.length ≤ 30) :
    ABlock config evm
      { contract := contract
        locals := (∅ : Store).insert "newSupplyQueue" (.array values)
        immutables := imms }
      supplyQueueBody (supplyQueuePrefixFrame evm imms values)
      (supplyQueueLoop :: supplyQueueTail) := by
  have he := supplyQueueLengthSource (evm := evm)
    (frame := supplyQueuePrefixFrame evm imms values) (values := values) (store_get_self _ _ _)
  simp only [hlen, decide_true] at he
  exact (supplyQueuePrefix evm imms values hwv hhi hrole).requireStep he

theorem supplyQueueBodyRevertsRole (evm : State) (imms : Store) (values : List Value)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hrole : ¬ allocatorRoleAllowed evm) :
    ExecTransitionBody config contract evm ((∅ : Store).insert "newSupplyQueue" (.array values))
      supplyQueueBody .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  exact ExecBlock.consRevert (allocatorRoleCallReverts evm _ imms "__role" hrole)

theorem supplyQueueBodyRevertsLength (evm : State) (imms : Store) (values : List Value)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hrole : allocatorRoleAllowed evm)
    (hlen : ¬ values.length ≤ 30) :
    ExecTransitionBody config contract evm ((∅ : Store).insert "newSupplyQueue" (.array values))
      supplyQueueBody .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply (supplyQueuePrefix evm imms values hwv hhi hrole).run
  have he := supplyQueueLengthSource (evm := evm)
    (frame := supplyQueuePrefixFrame evm imms values) (values := values) (store_get_self _ _ _)
  simp only [hlen, decide_false] at he
  exact ExecBlock.consRevert (ExecStmt.requireFalse he)

theorem supplyQueueBodyRevertsLoop (evm : State) (imms : Store) (values : List Value)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hrole : allocatorRoleAllowed evm)
    (hlen : values.length ≤ 30)
    (hloop : ExecForLoop config
      (supplyQueueIndexFrame (supplyQueuePrefixFrame evm imms values) 0) evm
      supplyQueueLoopCondition maxDepositPost supplyQueueLoopBody .reverted) :
    ExecTransitionBody config contract evm ((∅ : Store).insert "newSupplyQueue" (.array values))
      supplyQueueBody .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply (supplyQueueGuardPrefix evm imms values hwv hhi hrole hlen).run
  exact ExecBlock.consRevert (ExecStmt.for (supplyQueueForInit _ _) hloop)

theorem supplyQueueLoopPrefix (evm : State) (imms : Store) (values : List Value)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hrole : allocatorRoleAllowed evm)
    (hlen : values.length ≤ 30) {frame : Frame}
    (hloop : ExecForLoop config
      (supplyQueueIndexFrame (supplyQueuePrefixFrame evm imms values) 0) evm
      supplyQueueLoopCondition maxDepositPost supplyQueueLoopBody (.ok frame evm)) :
    ABlock config evm
      { contract := contract
        locals := (∅ : Store).insert "newSupplyQueue" (.array values)
        immutables := imms }
      supplyQueueBody frame supplyQueueTail := by
  constructor
  intro result htail
  apply (supplyQueueGuardPrefix evm imms values hwv hhi hrole hlen).run
  exact ExecBlock.consNormal (ExecStmt.for (supplyQueueForInit _ _) hloop) htail

theorem supplyQueueTailReturns {frame : Frame} {evm : State} {words : Nat → UInt256} {n i : Nat}
    (hready : SupplyQueueReady frame (wordArrayValues words 0 n) i) :
    ∃ final, ExecBlock config frame evm supplyQueueTail
      (.ok final (supplyQueueSourceState evm words n)) := by
  rcases frame with ⟨c, locals, imms⟩
  have hc : c = contract := hready.contract
  subst c
  refine ⟨⟨contract, locals.insert "__c2" (.address evm.executionEnv.source), imms⟩, ?_⟩
  refine ExecBlock.consNormal (supplyQueueAssign hready) ?_
  refine ExecBlock.consNormal
    (internalCallReturnExpr (retTy := [.elem .address]) (expr := .env .caller)
      (value := .address evm.executionEnv.source) (by rfl)
      (by simp only [evalExpr?, envValue, supplyQueueSourceState, pure])) ?_
  apply (ABlock.start.emitStep (vals := [.address evm.executionEnv.source,
    .array (wordArrayValues words 0 n)]) ?_).run
  · exact ExecBlock.nil
  · simp only [evalExprs?, evalExpr?, store_get_self,
      store_get_ne _ _ (by decide : ("__c2" == "newSupplyQueue") = false), hready.array,
      EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem supplyQueueTailStatic {frame : Frame} {evm : State} {words : Nat → UInt256} {n i : Nat}
    (hready : SupplyQueueReady frame (wordArrayValues words 0 n) i)
    (hperm : evm.executionEnv.perm = false) :
    ExecBlock config frame evm supplyQueueTail .staticViolation :=
  ExecBlock.consStatic (execStmt_assign_static (supplyQueueAssign hready) hperm)

end Benchmarks.Morpho.MetaMorphoV1_1

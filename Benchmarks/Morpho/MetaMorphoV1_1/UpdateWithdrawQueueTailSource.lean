import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueStorage

/-! Source outcomes of queue assignment and the final event. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

theorem updateWithdrawQueueTailReturns {frame : Frame} {evm : State} {imms : Store}
    {indexes : List Value} {curr i : Nat} {seen : List Bool} {queue : List UInt256}
    {cursor : UInt256}
    (h : UpdateWithdrawQueueReady frame imms indexes curr i seen queue cursor) :
    ∃ final, ExecBlock config frame evm updateWithdrawQueueTail
      (.ok final (updateWithdrawQueueSourceState evm queue)) := by
  rcases frame with ⟨c, locals, immutable⟩
  have hc : c = contract := h.contract
  subst c
  refine ⟨⟨contract, locals.insert "__c3" (.address evm.executionEnv.source), immutable⟩, ?_⟩
  refine ExecBlock.consNormal (updateWithdrawQueueAssign h) ?_
  refine ExecBlock.consNormal
    (internalCallReturnExpr (retTy := [.elem .address]) (expr := .env .caller)
      (value := .address evm.executionEnv.source) (by rfl)
      (by simp only [evalExpr?, envValue, updateWithdrawQueueSourceState, pure])) ?_
  apply (ABlock.start.emitStep (vals := [.address evm.executionEnv.source,
    .array (queue.map wordBytes32Value)]) ?_).run
  · exact ExecBlock.nil
  · simp only [evalExprs?, evalExpr?, store_get_self,
      store_get_ne _ _ (by decide : ("__c3" == "newWithdrawQueue") = false), h.queue,
      EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem updateWithdrawQueueTailStatic {frame : Frame} {evm : State} {imms : Store}
    {indexes : List Value} {curr i : Nat} {seen : List Bool} {queue : List UInt256}
    {cursor : UInt256}
    (h : UpdateWithdrawQueueReady frame imms indexes curr i seen queue cursor)
    (hperm : evm.executionEnv.perm = false) :
    ExecBlock config frame evm updateWithdrawQueueTail .staticViolation :=
  ExecBlock.consStatic (execStmt_assign_static (updateWithdrawQueueAssign h) hperm)

end Benchmarks.Morpho.MetaMorphoV1_1

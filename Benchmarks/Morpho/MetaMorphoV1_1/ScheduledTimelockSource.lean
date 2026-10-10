import Benchmarks.Morpho.MetaMorphoV1_1.SubmitTimelockSyntax

/-! Source execution of the deferred timelock update, including overflow and static failure. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

theorem scheduledTimelockTimeSource (evm : EVM.State) (imms : Store) (value : UInt256)
    (hfit : pendingTimelockScheduleFits evm) :
    evalExpr? config (scheduledTimelockFrame evm imms value)
      (pendingTimelockValueState evm value) scheduledTimelockTimeExpr =
      .ok (uint256Value (pendingTimeCastWord (pendingTimelockTime evm))) := by
  apply uint64CastSource
  apply checkedAddSourceOk (a := UInt256.ofNat evm.executionEnv.header.timestamp)
    (b := pendingTimelockDelay evm) ?_ ?_ hfit
  · simp only [evalExpr?, envValue, pendingTimelockValueState_executionEnv, pure]
  · simp only [evalExpr?, scheduledTimelockFrame, store_get_self, EvalResult.ofOption]

theorem scheduledTimelockTimeSourceRevert (evm : EVM.State) (imms : Store)
    (value : UInt256) (hover : ¬ pendingTimelockScheduleFits evm) :
    evalExpr? config (scheduledTimelockFrame evm imms value)
      (pendingTimelockValueState evm value) scheduledTimelockTimeExpr = .revert := by
  have h := checkedAddSourceOverflow
    (cfg := config) (solm := scheduledTimelockFrame evm imms value)
    (evm := pendingTimelockValueState evm value)
    (lhs := .env .timestamp) (rhs := .var "__pendingTime3")
    (a := UInt256.ofNat evm.executionEnv.header.timestamp) (b := pendingTimelockDelay evm)
    (by simp only [evalExpr?, envValue, pendingTimelockValueState_executionEnv, pure])
    (by simp only [evalExpr?, scheduledTimelockFrame, store_get_self, EvalResult.ofOption])
    (Nat.le_of_not_gt hover)
  simp only [scheduledTimelockTimeExpr, evalExpr?, h, bind, EvalResult.bind]


theorem scheduledTimelockRead (evm : EVM.State) (imms : Store) (value : UInt256) :
    ExecStmt config (submitTimelockFrame evm imms value) evm
      (.letDecl "__pendingTime3" (some (.elem (.int (.uint ⟨256, by decide⟩))))
        (.storage ⟨"timelock", []⟩))
      (.ok (scheduledTimelockFrame evm imms value) evm) := by
  apply ExecStmt.letDecl
  exact evalStorage_timelock evm _ imms (by
    simp [submitTimelockFrame, submitTimelockAdminFrame, adminFrame, submitTimelockLocals])

theorem scheduledTimelockValueAssign (evm : EVM.State) (imms : Store)
    (value : UInt256) (hbound : timelockInBounds value) :
    ExecStmt config (scheduledTimelockFrame evm imms value) evm
      (.assign .storage ⟨"pendingTimelock", [.field "value"]⟩ scheduledTimelockValueExpr)
      (.ok (scheduledTimelockFrame evm imms value) (pendingTimelockValueState evm value)) := by
  apply ExecStmt.assign (value := uint256Value value)
  · apply uintCastSource _ ?_ (by have := hbound.1; change _ < 2 ^ 184; omega)
    simp only [evalExpr?, scheduledTimelockFrame, submitTimelockFrame, submitTimelockAdminFrame,
      adminFrame,
      submitTimelockLocals,
      store_get_ne _ _ (by decide : ("__pendingTime3" == "newTimelock") = false),
      store_get_ne _ _ (by decide : ("__c1" == "newTimelock") = false),
      store_get_ne _ _ (by decide : ("__c0" == "newTimelock") = false),
      store_get_ne _ _ (by decide : ("__calldata" == "newTimelock") = false),
      store_get_self, EvalResult.ofOption]
  · exact assignPendingTimelockValue evm _ imms value (by
      simp [submitTimelockFrame, submitTimelockAdminFrame, adminFrame, submitTimelockLocals])

theorem scheduledTimelockSource (evm : EVM.State) (imms : Store) (value : UInt256)
    (hbound : timelockInBounds value) (hfit : pendingTimelockScheduleFits evm) :
    ExecBlock config (submitTimelockFrame evm imms value) evm scheduledTimelockBody
      (.ok (scheduledTimelockFrame evm imms value) (pendingTimelockScheduledState evm value)) := by
  refine ExecBlock.consNormal (scheduledTimelockRead evm imms value) ?_
  refine ExecBlock.consNormal (scheduledTimelockValueAssign evm imms value hbound) ?_
  refine ExecBlock.consNormal (ExecStmt.assign
    (scheduledTimelockTimeSource evm imms value hfit)
    (assignPendingTimelockTime _ _ imms (pendingTimelockTime evm) (by
      simp [submitTimelockFrame, submitTimelockAdminFrame, adminFrame,
        submitTimelockLocals]))) ?_
  apply (ABlock.start.emitStep (vals := [uint256Value value]) ?_).run
  · exact ExecBlock.nil
  · simp only [evalExprs?, evalExpr?, submitTimelockFrame, submitTimelockAdminFrame, adminFrame,
      submitTimelockLocals,
      store_get_ne _ _ (by decide : ("__pendingTime3" == "newTimelock") = false),
      store_get_ne _ _ (by decide : ("__c1" == "newTimelock") = false),
      store_get_ne _ _ (by decide : ("__c0" == "newTimelock") = false),
      store_get_ne _ _ (by decide : ("__calldata" == "newTimelock") = false),
      store_get_self, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem scheduledTimelockSourceStatic (evm : EVM.State) (imms : Store) (value : UInt256)
    (hbound : timelockInBounds value) (hperm : evm.executionEnv.perm = false) :
    ExecBlock config (submitTimelockFrame evm imms value) evm scheduledTimelockBody
      .staticViolation := by
  refine ExecBlock.consNormal (scheduledTimelockRead evm imms value) ?_
  exact ExecBlock.consStatic
    (execStmt_assign_static (scheduledTimelockValueAssign evm imms value hbound) hperm)

theorem scheduledTimelockSourceRevert (evm : EVM.State) (imms : Store) (value : UInt256)
    (hbound : timelockInBounds value) (hover : ¬ pendingTimelockScheduleFits evm) :
    ExecBlock config (submitTimelockFrame evm imms value) evm scheduledTimelockBody .reverted := by
  refine ExecBlock.consNormal (scheduledTimelockRead evm imms value) ?_
  refine ExecBlock.consNormal (scheduledTimelockValueAssign evm imms value hbound) ?_
  exact ExecBlock.consRevert
    (ExecStmt.assignExprRevert (scheduledTimelockTimeSourceRevert evm imms value hover))

end Benchmarks.Morpho.MetaMorphoV1_1

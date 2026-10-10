import Benchmarks.Morpho.MetaMorphoV1_1.SubmitGuardianSyntax

/-! Source execution of the deferred guardian update, including overflow and static failure. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

theorem scheduledGuardianRead (evm : EVM.State) (imms : Store) (value : AccountAddress) :
    ExecStmt config (submitGuardianFrame evm imms value) evm
      (.letDecl "__pendingTime2" (some (.elem (.int (.uint ⟨256, by decide⟩))))
        (.storage ⟨"timelock", []⟩))
      (.ok (scheduledGuardianFrame evm imms value) evm) := by
  apply ExecStmt.letDecl
  exact evalStorage_timelock evm _ imms (by
    simp [submitGuardianFrame, adminFrame, submitGuardianLocals])

theorem scheduledGuardianValueAssign (evm : EVM.State) (imms : Store)
    (value : AccountAddress) :
    ExecStmt config (scheduledGuardianFrame evm imms value) evm
      (.assign .storage ⟨"pendingGuardian", [.field "value"]⟩ (.var "newGuardian"))
      (.ok (scheduledGuardianFrame evm imms value) (pendingGuardianValueState evm value)) := by
  apply ExecStmt.assign (value := .address value)
  · simp only [evalExpr?, scheduledGuardianFrame, submitGuardianFrame, adminFrame,
      submitGuardianLocals,
      store_get_ne _ _ (by decide : ("__pendingTime2" == "newGuardian") = false),
      store_get_ne _ _ (by decide : ("__c0" == "newGuardian") = false),
      store_get_ne _ _ (by decide : ("__calldata" == "newGuardian") = false),
      store_get_self, EvalResult.ofOption]
  · exact assignPendingGuardianValue evm _ imms value (by
      simp [scheduledGuardianFrame, submitGuardianFrame, adminFrame, submitGuardianLocals])

theorem scheduledGuardianSource (evm : EVM.State) (imms : Store) (value : AccountAddress)
    (hfit : pendingGuardianScheduleFits evm) :
    ExecBlock config (submitGuardianFrame evm imms value) evm scheduledGuardianBody
      (.ok (scheduledGuardianFrame evm imms value) (pendingGuardianScheduledState evm value)) := by
  refine ExecBlock.consNormal (scheduledGuardianRead evm imms value) ?_
  refine ExecBlock.consNormal (scheduledGuardianValueAssign evm imms value) ?_
  refine ExecBlock.consNormal (ExecStmt.assign
    (scheduledGuardianTimeSource evm imms value hfit)
    (assignPendingGuardianTime _ _ imms (pendingGuardianTime evm) (by
      simp [scheduledGuardianFrame, submitGuardianFrame, adminFrame, submitGuardianLocals]))) ?_
  apply (ABlock.start.emitStep (vals := [.address value]) ?_).run
  · exact ExecBlock.nil
  · simp only [evalExprs?, evalExpr?, scheduledGuardianFrame, submitGuardianFrame, adminFrame,
      submitGuardianLocals,
      store_get_ne _ _ (by decide : ("__pendingTime2" == "newGuardian") = false),
      store_get_ne _ _ (by decide : ("__c0" == "newGuardian") = false),
      store_get_ne _ _ (by decide : ("__calldata" == "newGuardian") = false),
      store_get_self, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem scheduledGuardianSourceStatic (evm : EVM.State) (imms : Store) (value : AccountAddress)
    (hperm : evm.executionEnv.perm = false) :
    ExecBlock config (submitGuardianFrame evm imms value) evm scheduledGuardianBody
      .staticViolation := by
  refine ExecBlock.consNormal (scheduledGuardianRead evm imms value) ?_
  exact ExecBlock.consStatic
    (execStmt_assign_static (scheduledGuardianValueAssign evm imms value) hperm)

theorem scheduledGuardianSourceRevert (evm : EVM.State) (imms : Store) (value : AccountAddress)
    (hover : ¬ pendingGuardianScheduleFits evm) :
    ExecBlock config (submitGuardianFrame evm imms value) evm scheduledGuardianBody .reverted := by
  refine ExecBlock.consNormal (scheduledGuardianRead evm imms value) ?_
  refine ExecBlock.consNormal (scheduledGuardianValueAssign evm imms value) ?_
  exact ExecBlock.consRevert
    (ExecStmt.assignExprRevert (scheduledGuardianTimeSourceRevert evm imms value hover))

end Benchmarks.Morpho.MetaMorphoV1_1

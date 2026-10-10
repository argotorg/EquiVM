import Benchmarks.Morpho.MetaMorphoV1_1.ScheduledGuardianSource

/-! Complete source outcomes for submitting a guardian update. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def submitGuardianState (evm : EVM.State) (value : AccountAddress) : EVM.State :=
  if guardianAddress evm = AccountAddress.ofNat 0 then setGuardianState evm value
  else pendingGuardianScheduledState evm value

abbrev submitGuardianFits (evm : EVM.State) : Prop :=
  guardianAddress evm = AccountAddress.ofNat 0 ∨ pendingGuardianScheduleFits evm

theorem submitGuardianNewSource (evm : EVM.State) (imms : Store) (value : AccountAddress) :
    evalExpr? config (submitGuardianFrame evm imms value) evm (.var "newGuardian") =
      .ok (.address value) := by
  simp only [evalExpr?, submitGuardianFrame, adminFrame, submitGuardianLocals,
    store_get_ne _ _ (by decide : ("__c0" == "newGuardian") = false),
    store_get_ne _ _ (by decide : ("__calldata" == "newGuardian") = false),
    store_get_self, EvalResult.ofOption]

theorem submitGuardianBodyReturns (evm : EVM.State) (imms : Store) (value : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hgood : submitGuardianAllowed evm value) (hfit : submitGuardianFits evm) :
    ∃ final, ExecTransitionBody config contract evm (submitGuardianLocals value)
      submitGuardianTransition.body (.returned final (submitGuardianState evm value) none)
      imms := by
  by_cases hz : guardianAddress evm = AccountAddress.ofNat 0
  · rw [submitGuardianState, if_pos hz]
    refine ⟨⟨contract, (submitGuardianFrame evm imms value).locals.insert "__c1" .unit, imms⟩,
      ExecFuncBody.execBlockOK ?_⟩
    apply (submitGuardianPrefix evm imms value hwv hhi howner hgood).run
    refine ExecBlock.consNormal (ExecStmt.iteTrue ?_ ?_) ExecBlock.nil
    · simp only [submitGuardianImmediateSource, hz, decide_true]
    · exact ExecBlock.consNormal
        (setGuardianCall evm _ imms value _ "__c1" (submitGuardianNewSource evm imms value))
        ExecBlock.nil
  · rw [submitGuardianState, if_neg hz]
    refine ⟨scheduledGuardianFrame evm imms value, ExecFuncBody.execBlockOK ?_⟩
    apply (submitGuardianPrefix evm imms value hwv hhi howner hgood).run
    exact ExecBlock.consNormal (ExecStmt.iteFalse
      (by simp only [submitGuardianImmediateSource, hz, decide_false])
      (scheduledGuardianSource evm imms value (hfit.resolve_left hz))) ExecBlock.nil

theorem submitGuardianBodyStatic (evm : EVM.State) (imms : Store) (value : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hgood : submitGuardianAllowed evm value) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (submitGuardianLocals value)
      submitGuardianTransition.body .staticViolation imms := by
  apply ExecFuncBody.execBlockStatic
  apply (submitGuardianPrefix evm imms value hwv hhi howner hgood).run
  by_cases hz : guardianAddress evm = AccountAddress.ofNat 0
  · exact ExecBlock.consStatic (ExecStmt.iteTrue
      (by simp only [submitGuardianImmediateSource, hz, decide_true])
      (ExecBlock.consStatic (setGuardianCallStatic evm _ imms value _ "__c1"
        (submitGuardianNewSource evm imms value) hperm)))
  · exact ExecBlock.consStatic (ExecStmt.iteFalse
      (by simp only [submitGuardianImmediateSource, hz, decide_false])
      (scheduledGuardianSourceStatic evm imms value hperm))

theorem submitGuardianBodyRevertsGuard (evm : EVM.State) (imms : Store) (value : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hbad : ¬ submitGuardianAllowed evm value) :
    ExecTransitionBody config contract evm (submitGuardianLocals value)
      submitGuardianTransition.body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  have hpre := adminPrefix evm (submitGuardianLocals value) imms submitGuardianTail hwv hhi howner
  by_cases hd : value = guardianAddress evm
  · apply hpre.requireRevert
    change evalExpr? config (submitGuardianFrame evm imms value) evm submitGuardianDifferent = _
    simp [submitGuardianDifferentSource, hd]
  · have ht : pendingUpdateTime true (pendingUpdateWord true evm) ≠ ⟨0⟩ :=
      fun hz ↦ hbad ⟨hd, hz⟩
    apply (hpre.requireStep (by
      change evalExpr? config (submitGuardianFrame evm imms value) evm submitGuardianDifferent = _
      simp [submitGuardianDifferentSource, hd])).requireRevert
    change evalExpr? config (submitGuardianFrame evm imms value) evm submitGuardianNoPending = _
    simp only [submitGuardianNoPendingSource, ht, decide_false]

theorem submitGuardianBodyRevertsOverflow (evm : EVM.State) (imms : Store)
    (value : AccountAddress) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hgood : submitGuardianAllowed evm value) (hbad : ¬ submitGuardianFits evm) :
    ExecTransitionBody config contract evm (submitGuardianLocals value)
      submitGuardianTransition.body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply (submitGuardianPrefix evm imms value hwv hhi howner hgood).run
  have hn : guardianAddress evm ≠ AccountAddress.ofNat 0 := fun hz ↦ hbad (.inl hz)
  exact ExecBlock.consRevert (ExecStmt.iteFalse
    (by simp only [submitGuardianImmediateSource, hn, decide_false])
    (scheduledGuardianSourceRevert evm imms value (fun hfit ↦ hbad (.inr hfit))))

end Benchmarks.Morpho.MetaMorphoV1_1

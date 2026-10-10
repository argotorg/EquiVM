import Benchmarks.Morpho.MetaMorphoV1_1.ScheduledTimelockSource

/-! Complete source outcomes for submitting a timelock update. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def submitTimelockState (evm : EVM.State) (value : UInt256) : EVM.State :=
  if (pendingTimelockDelay evm).toNat < value.toNat then setTimelockState evm value
  else pendingTimelockScheduledState evm value

abbrev submitTimelockFits (evm : EVM.State) (value : UInt256) : Prop :=
  (pendingTimelockDelay evm).toNat < value.toNat ∨ pendingTimelockScheduleFits evm

theorem submitTimelockBodyReturns (evm : EVM.State) (imms : Store) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hgood : submitTimelockAllowed evm value) (hfit : submitTimelockFits evm value) :
    ∃ final, ExecTransitionBody config contract evm (submitTimelockLocals value)
      submitTimelockTransition.body (.returned final (submitTimelockState evm value) none)
      imms := by
  by_cases hz : (pendingTimelockDelay evm).toNat < value.toNat
  · rw [submitTimelockState, if_pos hz]
    refine ⟨⟨contract, (submitTimelockFrame evm imms value).locals.insert "__c2" .unit, imms⟩,
      ExecFuncBody.execBlockOK ?_⟩
    apply (submitTimelockPrefix evm imms value hwv hhi howner hgood).run
    refine ExecBlock.consNormal (ExecStmt.iteTrue ?_ ?_) ExecBlock.nil
    · simp only [submitTimelockImmediateSource, hz, decide_true]
    · exact ExecBlock.consNormal
        (setTimelockCall evm _ imms value _ "__c2" (submitTimelockNewSource evm imms value))
        ExecBlock.nil
  · rw [submitTimelockState, if_neg hz]
    refine ⟨scheduledTimelockFrame evm imms value, ExecFuncBody.execBlockOK ?_⟩
    apply (submitTimelockPrefix evm imms value hwv hhi howner hgood).run
    exact ExecBlock.consNormal (ExecStmt.iteFalse
      (by simp only [submitTimelockImmediateSource, hz, decide_false])
      (scheduledTimelockSource evm imms value hgood.2.2 (hfit.resolve_left hz))) ExecBlock.nil

theorem submitTimelockBodyStatic (evm : EVM.State) (imms : Store) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hgood : submitTimelockAllowed evm value) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (submitTimelockLocals value)
      submitTimelockTransition.body .staticViolation imms := by
  apply ExecFuncBody.execBlockStatic
  apply (submitTimelockPrefix evm imms value hwv hhi howner hgood).run
  by_cases hz : (pendingTimelockDelay evm).toNat < value.toNat
  · exact ExecBlock.consStatic (ExecStmt.iteTrue
      (by simp only [submitTimelockImmediateSource, hz, decide_true])
      (ExecBlock.consStatic (setTimelockCallStatic evm _ imms value _ "__c2"
        (submitTimelockNewSource evm imms value) hperm)))
  · exact ExecBlock.consStatic (ExecStmt.iteFalse
      (by simp only [submitTimelockImmediateSource, hz, decide_false])
      (scheduledTimelockSourceStatic evm imms value hgood.2.2 hperm))

theorem submitTimelockBodyRevertsGuard (evm : EVM.State) (imms : Store) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hbad : ¬ submitTimelockAllowed evm value) :
    ExecTransitionBody config contract evm (submitTimelockLocals value)
      submitTimelockTransition.body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  have hpre := adminPrefix evm (submitTimelockLocals value) imms submitTimelockTail hwv hhi howner
  by_cases hd : value = pendingTimelockDelay evm
  · apply hpre.requireRevert
    change evalExpr? config (submitTimelockAdminFrame evm imms value) evm
      submitTimelockDifferent = _
    simp [submitTimelockDifferentSource, hd]
  · have hg := hpre.requireStep (by
      change evalExpr? config (submitTimelockAdminFrame evm imms value) evm
        submitTimelockDifferent = _
      simp [submitTimelockDifferentSource, hd])
    by_cases ht : pendingUpdateTime false (pendingUpdateWord false evm) = ⟨0⟩
    · apply (hg.requireStep (by
        change evalExpr? config (submitTimelockAdminFrame evm imms value) evm
          submitTimelockNoPending = _
        simp only [submitTimelockNoPendingSource, ht, decide_true])).run
      exact ExecBlock.consRevert (timelockBoundsCallReverts evm _ imms value _ "__c1"
        (fun hb ↦ hbad ⟨hd, ht, hb⟩) (submitTimelockAdminNewSource evm imms value))
    · apply hg.requireRevert
      change evalExpr? config (submitTimelockAdminFrame evm imms value) evm
        submitTimelockNoPending = _
      simp only [submitTimelockNoPendingSource, ht, decide_false]

theorem submitTimelockBodyRevertsOverflow (evm : EVM.State) (imms : Store)
    (value : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hgood : submitTimelockAllowed evm value) (hbad : ¬ submitTimelockFits evm value) :
    ExecTransitionBody config contract evm (submitTimelockLocals value)
      submitTimelockTransition.body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply (submitTimelockPrefix evm imms value hwv hhi howner hgood).run
  have hn : ¬ (pendingTimelockDelay evm).toNat < value.toNat := fun hz ↦ hbad (.inl hz)
  exact ExecBlock.consRevert (ExecStmt.iteFalse
    (by simp only [submitTimelockImmediateSource, hn, decide_false])
    (scheduledTimelockSourceRevert evm imms value hgood.2.2 (fun hfit ↦ hbad (.inr hfit))))

end Benchmarks.Morpho.MetaMorphoV1_1

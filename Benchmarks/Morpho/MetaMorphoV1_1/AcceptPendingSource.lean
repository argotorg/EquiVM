import Benchmarks.Morpho.MetaMorphoV1_1.AcceptPendingSyntax

/-! Source executions of timelock and guardian acceptance. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

theorem acceptPendingCallSource (guardian : Bool) (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? (revocationName guardian) = none) :
    ExecStmt config (acceptPendingFrame guardian evm locals imms) evm
      (acceptPendingCall guardian)
      (.ok ⟨contract, (acceptPendingFrame guardian evm locals imms).locals.insert "__c0" .unit,
        imms⟩ (acceptPendingState guardian evm)) := by
  cases guardian
  · apply setTimelockCall
    exact evalStorage_pendingTimelockValue evm _ imms (by
      simpa [acceptPendingFrame, revocationName] using hbase)
  · apply setGuardianCall
    exact evalStorage_pendingGuardianValue evm _ imms (by
      simpa [acceptPendingFrame, revocationName] using hbase)

theorem acceptPendingCallSourceStatic (guardian : Bool) (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? (revocationName guardian) = none)
    (hperm : evm.executionEnv.perm = false) :
    ExecStmt config (acceptPendingFrame guardian evm locals imms) evm
      (acceptPendingCall guardian) .staticViolation := by
  cases guardian
  · exact setTimelockCallStatic evm _ imms _ _ _
      (evalStorage_pendingTimelockValue evm _ imms (by
        simpa [acceptPendingFrame, revocationName] using hbase)) hperm
  · exact setGuardianCallStatic evm _ imms _ _ _
      (evalStorage_pendingGuardianValue evm _ imms (by
        simpa [acceptPendingFrame, revocationName] using hbase)) hperm

theorem acceptPendingBodyReturns (guardian : Bool) (evm : EVM.State) (locals imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbase : locals.get? (revocationName guardian) = none)
    (hgood : acceptPendingAllowed guardian evm) :
    ∃ final, ExecTransitionBody config contract evm locals (acceptPendingBody guardian)
      (.returned final (acceptPendingState guardian evm) none) imms := by
  refine ⟨⟨contract, (acceptPendingFrame guardian evm locals imms).locals.insert "__c0" .unit,
    imms⟩, ExecFuncBody.execBlockOK ?_⟩
  apply (acceptPendingPrefix guardian evm locals imms hwv hhi hbase hgood).run
  exact ExecBlock.consNormal (acceptPendingCallSource guardian evm locals imms hbase) ExecBlock.nil

theorem acceptPendingBodyStatic (guardian : Bool) (evm : EVM.State) (locals imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbase : locals.get? (revocationName guardian) = none)
    (hgood : acceptPendingAllowed guardian evm) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm locals (acceptPendingBody guardian)
      .staticViolation imms := by
  apply ExecFuncBody.execBlockStatic
  apply (acceptPendingPrefix guardian evm locals imms hwv hhi hbase hgood).run
  exact ExecBlock.consStatic (acceptPendingCallSourceStatic guardian evm locals imms hbase hperm)

theorem acceptPendingBodyReverts (guardian : Bool) (evm : EVM.State) (locals imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbase : locals.get? (revocationName guardian) = none)
    (hbad : ¬ acceptPendingAllowed guardian evm) :
    ExecTransitionBody config contract evm locals (acceptPendingBody guardian) .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  by_cases hz : pendingUpdateTime guardian (pendingUpdateWord guardian evm) = ⟨0⟩
  · exact (acceptPendingRead guardian evm locals imms hwv hhi hbase).requireRevert (by
      simp [acceptPendingNonzeroSource, hz])
  · have ht : ¬ (pendingUpdateTime guardian (pendingUpdateWord guardian evm)).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat := fun ht ↦ hbad ⟨hz, ht⟩
    exact ((acceptPendingRead guardian evm locals imms hwv hhi hbase).requireStep (by
      simp [acceptPendingNonzeroSource, hz])).requireRevert (by
        simp only [acceptPendingTimeSource, ht, decide_false])

end Benchmarks.Morpho.MetaMorphoV1_1

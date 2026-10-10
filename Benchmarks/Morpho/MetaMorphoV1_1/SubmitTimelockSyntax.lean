import Benchmarks.Morpho.MetaMorphoV1_1.PendingTimelockMutation
import Benchmarks.Morpho.MetaMorphoV1_1.AcceptPendingSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.TimelockBoundsSource
import Benchmarks.Morpho.MetaMorphoV1_1.MarketBalancesSource
import Benchmarks.Morpho.MetaMorphoV1_1.Uint128Cast

/-! Source expressions and frames for submitting a timelock update. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def submitTimelockLocals (value : UInt256) : Store :=
  (∅ : Store).insert "newTimelock" (uint256Value value)

def submitTimelockAdminFrame (evm : EVM.State) (imms : Store) (value : UInt256) : Frame :=
  adminFrame evm (submitTimelockLocals value) imms

def submitTimelockFrame (evm : EVM.State) (imms : Store) (value : UInt256) : Frame :=
  ⟨contract, (submitTimelockAdminFrame evm imms value).locals.insert "__c1" .unit, imms⟩

def scheduledTimelockFrame (evm : EVM.State) (imms : Store) (value : UInt256) : Frame :=
  ⟨contract, (submitTimelockFrame evm imms value).locals.insert "__pendingTime3"
    (uint256Value (pendingTimelockDelay evm)), imms⟩

def submitTimelockDifferent : Expr :=
  .binary .ne (.var "newTimelock") (.storage ⟨"timelock", []⟩)

def submitTimelockNoPending : Expr :=
  .binary .eq (.storage ⟨"pendingTimelock", [.field "validAt"]⟩) (.intLit 0)

def submitTimelockImmediate : Expr :=
  .binary .gt (.var "newTimelock") (.storage ⟨"timelock", []⟩)

def scheduledTimelockTimeExpr : Expr :=
  .cast (.inRange (.uint ⟨256, by decide⟩)
    (.binary .add (.env .timestamp) (.var "__pendingTime3")))
    (.elem (.int (.uint ⟨64, by decide⟩)))

def scheduledTimelockValueExpr : Expr :=
  .cast (.var "newTimelock") (.elem (.int (.uint ⟨184, by decide⟩)))

def scheduledTimelockBody : List Stmt :=
  [.letDecl "__pendingTime3" (some (.elem (.int (.uint ⟨256, by decide⟩))))
      (.storage ⟨"timelock", []⟩),
    .assign .storage ⟨"pendingTimelock", [.field "value"]⟩ scheduledTimelockValueExpr,
    .assign .storage ⟨"pendingTimelock", [.field "validAt"]⟩ scheduledTimelockTimeExpr,
    .emit "SubmitTimelock" [.var "newTimelock"]]

def submitTimelockBranch : Stmt :=
  .ite submitTimelockImmediate [.internalCall "_setTimelock" [.var "newTimelock"] "__c2"]
    scheduledTimelockBody

def submitTimelockTail : List Stmt :=
  [.require submitTimelockDifferent, .require submitTimelockNoPending,
    .internalCall "_checkTimelockBounds" [.var "newTimelock"] "__c1", submitTimelockBranch]

abbrev submitTimelockAllowed (evm : EVM.State) (value : UInt256) : Prop :=
  value ≠ pendingTimelockDelay evm ∧
    pendingUpdateTime false (pendingUpdateWord false evm) = ⟨0⟩ ∧ timelockInBounds value

theorem submitTimelockAdminNewSource (evm : EVM.State) (imms : Store) (value : UInt256) :
    evalExpr? config (submitTimelockAdminFrame evm imms value) evm (.var "newTimelock") =
      .ok (uint256Value value) := by
  simp only [evalExpr?, submitTimelockAdminFrame, adminFrame, submitTimelockLocals,
    store_get_ne _ _ (by decide : ("__c0" == "newTimelock") = false),
    store_get_ne _ _ (by decide : ("__calldata" == "newTimelock") = false),
    store_get_self, EvalResult.ofOption]

theorem submitTimelockNewSource (evm : EVM.State) (imms : Store) (value : UInt256) :
    evalExpr? config (submitTimelockFrame evm imms value) evm (.var "newTimelock") =
      .ok (uint256Value value) := by
  simp only [evalExpr?, submitTimelockFrame,
    store_get_ne _ _ (by decide : ("__c1" == "newTimelock") = false)]
  simpa only [evalExpr?] using submitTimelockAdminNewSource evm imms value

theorem submitTimelockDifferentSource (evm : EVM.State) (imms : Store) (value : UInt256) :
    evalExpr? config (submitTimelockAdminFrame evm imms value) evm submitTimelockDifferent =
      .ok (.bool (decide (value ≠ pendingTimelockDelay evm))) := by
  apply SourceMemory.wordNeSource (submitTimelockAdminNewSource evm imms value)
  exact evalStorage_timelock evm _ imms (by
    simp [submitTimelockAdminFrame, adminFrame, submitTimelockLocals])

theorem submitTimelockNoPendingSource (evm : EVM.State) (imms : Store) (value : UInt256) :
    evalExpr? config (submitTimelockAdminFrame evm imms value) evm submitTimelockNoPending =
      .ok (.bool (decide (pendingUpdateTime false (pendingUpdateWord false evm) = ⟨0⟩))) := by
  have ht := evalStorage_pendingTimelockValidAt evm
    (submitTimelockAdminFrame evm imms value).locals imms (by
      simp [submitTimelockAdminFrame, adminFrame, submitTimelockLocals])
  change evalExpr? config (submitTimelockAdminFrame evm imms value) evm
    (.storage ⟨"pendingTimelock", [.field "validAt"]⟩) =
    .ok (uint256Value (pendingUpdateTime false (pendingUpdateWord false evm))) at ht
  rw [submitTimelockNoPending, evalExpr_binary_nonshort (by decide) (by decide)]
  have hz : (pendingUpdateTime false (pendingUpdateWord false evm)).toNat = 0 ↔
      pendingUpdateTime false (pendingUpdateWord false evm) = ⟨0⟩ :=
    ⟨uint256_toNat_eq_zero, fun h ↦ by rw [h]; rfl⟩
  simp [ht, evalExpr?, pure, bind, EvalResult.bind, evalBinaryOp?, uint256Value, BEq.beq, hz]

theorem submitTimelockImmediateSource (evm : EVM.State) (imms : Store) (value : UInt256) :
    evalExpr? config (submitTimelockFrame evm imms value) evm submitTimelockImmediate =
      .ok (.bool (decide ((pendingTimelockDelay evm).toNat < value.toNat))) := by
  have ht := evalStorage_timelock evm (submitTimelockFrame evm imms value).locals imms (by
    simp [submitTimelockFrame, submitTimelockAdminFrame, adminFrame, submitTimelockLocals])
  change evalExpr? config (submitTimelockFrame evm imms value) evm
    (.storage ⟨"timelock", []⟩) = .ok (uint256Value (pendingTimelockDelay evm)) at ht
  rw [submitTimelockImmediate, evalExpr_binary_nonshort (by decide) (by decide)]
  simp only [submitTimelockNewSource, ht, bind, EvalResult.bind, evalBinaryOp?, uint256Value]
  simp only [Int.ofNat_eq_natCast, Nat.cast_lt]

theorem submitTimelockPrefix (evm : EVM.State) (imms : Store) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hgood : submitTimelockAllowed evm value) :
    ABlock config evm ⟨contract, submitTimelockLocals value, imms⟩
      submitTimelockTransition.body (submitTimelockFrame evm imms value)
      [submitTimelockBranch] := by
  have hpre := adminPrefix evm (submitTimelockLocals value) imms submitTimelockTail hwv hhi howner
  have hg := (hpre.requireStep (by
    change evalExpr? config (submitTimelockAdminFrame evm imms value) evm
      submitTimelockDifferent = _
    simp [submitTimelockDifferentSource, hgood.1])).requireStep (by
    change evalExpr? config (submitTimelockAdminFrame evm imms value) evm
      submitTimelockNoPending = _
    simp only [submitTimelockNoPendingSource, hgood.2.1, decide_true])
  exact ⟨fun h ↦ hg.run (ExecBlock.consNormal
    (timelockBoundsCall evm _ imms value _ "__c1" hgood.2.2
      (submitTimelockAdminNewSource evm imms value)) h)⟩

end Benchmarks.Morpho.MetaMorphoV1_1

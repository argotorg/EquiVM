import Benchmarks.Morpho.MetaMorphoV1_1.PendingGuardianMutation
import Benchmarks.Morpho.MetaMorphoV1_1.AcceptPendingSyntax

/-! Source expressions and frames for submitting a guardian update. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def submitGuardianLocals (value : AccountAddress) : Store :=
  (∅ : Store).insert "newGuardian" (.address value)

def submitGuardianFrame (evm : EVM.State) (imms : Store) (value : AccountAddress) : Frame :=
  adminFrame evm (submitGuardianLocals value) imms

def scheduledGuardianFrame (evm : EVM.State) (imms : Store) (value : AccountAddress) : Frame :=
  { contract := contract
    locals := (submitGuardianFrame evm imms value).locals.insert "__pendingTime2"
      (uint256Value (pendingGuardianDelay evm))
    immutables := imms }

def submitGuardianDifferent : Expr :=
  .binary .ne (.var "newGuardian") (.storage ⟨"guardian", []⟩)

def submitGuardianNoPending : Expr :=
  .binary .eq (.storage ⟨"pendingGuardian", [.field "validAt"]⟩) (.intLit 0)

def submitGuardianImmediate : Expr :=
  .binary .eq (.storage ⟨"guardian", []⟩) (.cast (.intLit 0) (.elem .address))

def scheduledGuardianTimeExpr : Expr :=
  .cast (.inRange (.uint ⟨256, by decide⟩)
    (.binary .add (.env .timestamp) (.var "__pendingTime2")))
    (.elem (.int (.uint ⟨64, by decide⟩)))

def scheduledGuardianBody : List Stmt :=
  [.letDecl "__pendingTime2" (some (.elem (.int (.uint ⟨256, by decide⟩))))
      (.storage ⟨"timelock", []⟩),
    .assign .storage ⟨"pendingGuardian", [.field "value"]⟩ (.var "newGuardian"),
    .assign .storage ⟨"pendingGuardian", [.field "validAt"]⟩ scheduledGuardianTimeExpr,
    .emit "SubmitGuardian" [.var "newGuardian"]]

def submitGuardianBranch : Stmt :=
  .ite submitGuardianImmediate [.internalCall "_setGuardian" [.var "newGuardian"] "__c1"]
    scheduledGuardianBody

def submitGuardianTail : List Stmt :=
  [.require submitGuardianDifferent, .require submitGuardianNoPending, submitGuardianBranch]

abbrev submitGuardianAllowed (evm : EVM.State) (value : AccountAddress) : Prop :=
  value ≠ guardianAddress evm ∧ pendingUpdateTime true (pendingUpdateWord true evm) = ⟨0⟩

theorem submitGuardianDifferentSource (evm : EVM.State) (imms : Store) (value : AccountAddress) :
    evalExpr? config (submitGuardianFrame evm imms value) evm submitGuardianDifferent =
      .ok (.bool (decide (value ≠ guardianAddress evm))) := by
  apply evalExpr_addressNe
  · simp only [evalExpr?, submitGuardianFrame, adminFrame, submitGuardianLocals,
      store_get_ne _ _ (by decide : ("__c0" == "newGuardian") = false),
      store_get_ne _ _ (by decide : ("__calldata" == "newGuardian") = false),
      store_get_self, EvalResult.ofOption]
  · exact evalStorage_guardian evm _ imms (by
      simp [submitGuardianFrame, adminFrame, submitGuardianLocals])

theorem submitGuardianNoPendingSource (evm : EVM.State) (imms : Store)
    (value : AccountAddress) :
    evalExpr? config (submitGuardianFrame evm imms value) evm submitGuardianNoPending =
      .ok (.bool (decide (pendingUpdateTime true (pendingUpdateWord true evm) = ⟨0⟩))) := by
  have ht := evalStorage_pendingGuardianValidAt evm
    (submitGuardianFrame evm imms value).locals imms (by
      simp [submitGuardianFrame, adminFrame, submitGuardianLocals])
  change evalExpr? config (submitGuardianFrame evm imms value) evm
    (.storage ⟨"pendingGuardian", [.field "validAt"]⟩) =
    .ok (uint256Value (pendingUpdateTime true (pendingUpdateWord true evm))) at ht
  rw [submitGuardianNoPending, evalExpr_binary_nonshort (by decide) (by decide)]
  have hz : (pendingUpdateTime true (pendingUpdateWord true evm)).toNat = 0 ↔
      pendingUpdateTime true (pendingUpdateWord true evm) = ⟨0⟩ :=
    ⟨uint256_toNat_eq_zero, fun h ↦ by rw [h]; rfl⟩
  simp [ht, evalExpr?, pure, bind, EvalResult.bind, evalBinaryOp?, uint256Value, BEq.beq, hz]

theorem submitGuardianImmediateSource (evm : EVM.State) (imms : Store)
    (value : AccountAddress) :
    evalExpr? config (submitGuardianFrame evm imms value) evm submitGuardianImmediate =
      .ok (.bool (decide (guardianAddress evm = AccountAddress.ofNat 0))) := by
  apply evalExpr_addressEq
  · exact evalStorage_guardian evm _ imms (by
      simp [submitGuardianFrame, adminFrame, submitGuardianLocals])
  · simp [evalExpr?, castValue?, pure, bind, EvalResult.bind, EvalResult.ofOption]

theorem submitGuardianPrefix (evm : EVM.State) (imms : Store) (value : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hgood : submitGuardianAllowed evm value) :
    ABlock config evm ⟨contract, submitGuardianLocals value, imms⟩
      submitGuardianTransition.body (submitGuardianFrame evm imms value)
      [submitGuardianBranch] := by
  have hpre := adminPrefix evm (submitGuardianLocals value) imms submitGuardianTail hwv hhi howner
  apply (hpre.requireStep (by
    change evalExpr? config (submitGuardianFrame evm imms value) evm submitGuardianDifferent = _
    simp [submitGuardianDifferentSource, hgood.1])).requireStep
  change evalExpr? config (submitGuardianFrame evm imms value) evm submitGuardianNoPending = _
  simp only [submitGuardianNoPendingSource, hgood.2, decide_true]

theorem scheduledGuardianTimeSource (evm : EVM.State) (imms : Store) (value : AccountAddress)
    (hfit : pendingGuardianScheduleFits evm) :
    evalExpr? config (scheduledGuardianFrame evm imms value)
      (pendingGuardianValueState evm value) scheduledGuardianTimeExpr =
      .ok (uint256Value (pendingTimeCastWord (pendingGuardianTime evm))) := by
  apply uint64CastSource
  apply checkedAddSourceOk (a := UInt256.ofNat evm.executionEnv.header.timestamp)
    (b := pendingGuardianDelay evm) ?_ ?_ hfit
  · simp only [evalExpr?, envValue, pendingGuardianValueState_executionEnv, pure]
  · simp only [evalExpr?, scheduledGuardianFrame, store_get_self, EvalResult.ofOption]

theorem scheduledGuardianTimeSourceRevert (evm : EVM.State) (imms : Store)
    (value : AccountAddress) (hover : ¬ pendingGuardianScheduleFits evm) :
    evalExpr? config (scheduledGuardianFrame evm imms value)
      (pendingGuardianValueState evm value) scheduledGuardianTimeExpr = .revert := by
  have h := checkedAddSourceOverflow
    (cfg := config) (solm := scheduledGuardianFrame evm imms value)
    (evm := pendingGuardianValueState evm value)
    (lhs := .env .timestamp) (rhs := .var "__pendingTime2")
    (a := UInt256.ofNat evm.executionEnv.header.timestamp) (b := pendingGuardianDelay evm)
    (by simp only [evalExpr?, envValue, pendingGuardianValueState_executionEnv, pure])
    (by simp only [evalExpr?, scheduledGuardianFrame, store_get_self, EvalResult.ofOption])
    (Nat.le_of_not_gt hover)
  simp only [scheduledGuardianTimeExpr, evalExpr?, h, bind, EvalResult.bind]

end Benchmarks.Morpho.MetaMorphoV1_1

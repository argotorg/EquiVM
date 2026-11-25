import Benchmarks.Midnight.AdminSource

/-! The shared caller-or-delegate guard for operations performed on behalf of an account. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def authorizationSlot (authorizer authorized : UInt256) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨3⟩ authorizer) authorized

def authorizationWord (evm : EVM.State) (authorizer authorized : UInt256) : UInt256 :=
  UInt256.land (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
    (authorizationSlot authorizer authorized)) ⟨255⟩

def onBehalfAllowed (evm : EVM.State) (user : UInt256) : Prop :=
  user = solcSourceWord evm.executionEnv ∨
    authorizationWord evm user (solcSourceWord evm.executionEnv) ≠ ⟨0⟩

instance (evm : EVM.State) (user : UInt256) : Decidable (onBehalfAllowed evm user) :=
  inferInstanceAs (Decidable (_ ∨ _))

def onBehalfGuard : Expr := .binary .or (.binary .eq (.var "onBehalf") (.env .caller))
  (.storage { base := "isAuthorized", steps := [.mindex (.var "onBehalf"), .mindex (.env .caller)] })

theorem evalAuthorization {frame : Frame} {evm : EVM.State}
    (authorizer authorized : UInt256) (e0 e1 : Expr)
    (hc0 : authorizer.toNat < EVM.addressModulus) (hc1 : authorized.toNat < EVM.addressModulus)
    (hcontract : frame.contract = contract) (hbase : frame.locals.get? "isAuthorized" = none)
    (he0 : evalExpr? config frame evm e0 = .ok (.address (AccountAddress.ofNat authorizer.toNat)))
    (he1 : evalExpr? config frame evm e1 = .ok (.address (AccountAddress.ofNat authorized.toNat))) :
    evalExpr? config frame evm
      (.storage { base := "isAuthorized", steps := [.mindex e0, .mindex e1] }) =
      .ok (.bool (decide (authorizationWord evm authorizer authorized ≠ ⟨0⟩))) := by
  have hr : evalExpr? config frame evm
      (.storage { base := "isAuthorized", steps := [.mindex e0, .mindex e1] }) =
      .ok (wordToElem .bool (authorizationWord evm authorizer authorized)) := by
    apply evalExpr_storage_scalar_value
      (loc := boolOffset0Loc (authorizationSlot authorizer authorized))
      (er := { base := "isAuthorized", steps :=
        [.mindex (.address (AccountAddress.ofNat authorizer.toNat)),
         .mindex (.address (AccountAddress.ofNat authorized.toNat))] }) (t := .bool) hbase
    · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, he0, he1,
        EvalResult.bind, EvalResult.ofOption, valueToKey?, pure, bind]
    · rw [hcontract]; rfl
    · rfl
    · change some (StorageAddr.leaf (boolOffset0Loc (solcMappingSlot
        (solcMappingSlot ⟨3⟩ (keyValueToWord (.address (AccountAddress.ofNat authorizer.toNat))))
        (keyValueToWord (.address (AccountAddress.ofNat authorized.toNat)))))) = _
      rw [keyValueToWord_address_of_canonical authorizer hc0,
        keyValueToWord_address_of_canonical authorized hc1]
      rfl
    · exact storageLocLoad_bool_offset0 evm _
  simpa only [wordToElemBool, decide_not] using hr

theorem evalOnBehalfGuard {frame : Frame} (evm : EVM.State) (user : UInt256)
    (hcanon : user.toNat < EVM.addressModulus) (hcontract : frame.contract = contract)
    (hbase : frame.locals.get? "isAuthorized" = none)
    (hget : frame.locals.get? "onBehalf" = some (.address (AccountAddress.ofNat user.toNat))) :
    evalExpr? config frame evm onBehalfGuard = .ok (.bool (decide (onBehalfAllowed evm user))) := by
  have heq : evalExpr? config frame evm (.binary .eq (.var "onBehalf") (.env .caller)) =
      .ok (.bool (decide (user = solcSourceWord evm.executionEnv))) := by
    rw [evalExpr_binary_nonshort (by decide : BinaryOp.eq ≠ .and)
      (by decide : BinaryOp.eq ≠ .or)]
    simp only [evalExpr?, hget, EvalResult.ofOption, envValue, bind, pure, EvalResult.bind,
      evalBinaryOp?, Reasoning.VyperDispatch.value_address_beq]
    have hh : (AccountAddress.ofNat user.toNat = evm.executionEnv.source) ↔
        user = solcSourceWord evm.executionEnv := by
      rw [eq_comm, sourceAddress_eq_iff evm.executionEnv user hcanon, eq_comm]
    simp only [hh]
  have hread := evalAuthorization (evm := evm) user (solcSourceWord evm.executionEnv)
    (.var "onBehalf") (.env .caller) hcanon (solcSourceWord_canonical _) hcontract hbase
    (by simp only [evalExpr?, hget, EvalResult.ofOption])
    (by simp only [evalExpr?, envValue, solcSource_ofNat, pure])
  change evalExpr? config frame evm (.binary .or _ _) = _
  rw [evalExpr?, heq]
  by_cases hself : user = solcSourceWord evm.executionEnv
  · simp [hself, onBehalfAllowed, EvalResult.bind, bind, pure]
  · simp [hself, onBehalfAllowed, EvalResult.bind, bind, pure, hread]

end Benchmarks.Midnight

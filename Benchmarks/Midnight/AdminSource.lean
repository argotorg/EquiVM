import Benchmarks.Midnight.AliasStorage
import Benchmarks.Midnight.InternalCall
import Reasoning.VyperDispatch

/-! Shared authorization and address storage updates for Midnight's administrative setters. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

-- LIBRARY CANDIDATE: a function with no return parameters falls through to empty returndata.
theorem voidReturnEquiv : returnEquiv ByteArray.empty none [] :=
  .fallthrough rfl rfl (by native_decide)

def adminAllowed (evm : EVM.State) : Prop :=
  solcSourceWord evm.executionEnv = UInt256.land
    (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩) solcAddrMask

instance (evm : EVM.State) : Decidable (adminAllowed evm) := inferInstanceAs (Decidable (_ = _))

def adminGuard : Expr := .binary .eq (.env .caller) (.storage { base := "configurator" })

theorem evalAdminGuard {frame : Frame} (evm : EVM.State)
    (hcontract : frame.contract = contract) (hbase : frame.locals.get? "configurator" = none) :
    evalExpr? config frame evm adminGuard = .ok (.bool (decide (adminAllowed evm))) := by
  have hread : evalExpr? config frame evm (.storage { base := "configurator" }) =
      .ok (.address (AccountAddress.ofNat (UInt256.land
        (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩) solcAddrMask).toNat)) := by
    apply evalExpr_storage_scalar_value (loc := addressOffset0Loc ⟨9⟩)
      (er := { base := "configurator" }) (t := .address) hbase
      (by simp [evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind])
      (by rw [hcontract]; rfl) rfl rfl (storageLocLoad_address_offset0 evm ⟨9⟩)
  rw [show adminGuard = .binary .eq (.env .caller) (.storage { base := "configurator" }) from rfl,
    evalExpr_binary_nonshort (by decide : BinaryOp.eq ≠ .and) (by decide : BinaryOp.eq ≠ .or)]
  simp only [evalExpr?, envValue, hread, bind, pure, EvalResult.bind, evalBinaryOp?,
    Reasoning.VyperDispatch.value_address_beq]
  simp only [sourceAddress_eq_iff evm.executionEnv _ (solcAddrMask_result_canonical _)]
  rfl

def addressUpdateState (evm : EVM.State) (slot value : UInt256) : EVM.State :=
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot
    (setAddressOffset0Word (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) value)

theorem assignAddressVariable {frame : Frame} {evm : EVM.State} {name : Ident}
    (slot value : UInt256) (hcanon : value.toNat < EVM.addressModulus)
    (hbase : frame.locals.get? name = none)
    (hty : storageTypeAt? frame.contract.storage { base := name } = some (.elem .address))
    (hloc : midnightStorageLayout { base := name } = some (.leaf (addressOffset0Loc slot))) :
    assignStorageRef? config frame evm .storage { base := name }
      (.address (AccountAddress.ofNat value.toNat)) =
      .ok (frame, addressUpdateState evm slot value) := by
  exact assignStorageRef_storage_scalar_value hbase
    (by simp [evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind]) hty rfl hloc (Or.inl ⟨_, rfl⟩)
    (storageLocStore_address_offset0 evm slot value hcanon)

def adminAddressArguments (arg : Ident) (value : UInt256) : Store :=
  (∅ : Store).insert arg (.address (AccountAddress.ofNat value.toNat))

def adminAddressBody (name arg event : Ident) : List Stmt :=
  entryPrefix ++ [.require adminGuard, .assign .storage { base := name } (.var arg),
    .emit event [.var arg]]

theorem adminArgumentEval (evm : EVM.State) (arg : Ident) (value : UInt256)
    (harg : arg ≠ "__calldata") :
    evalExpr? config (calldataFrame contract (adminAddressArguments arg value) ∅ evm) evm
      (.var arg) = .ok (.address (AccountAddress.ofNat value.toNat)) := by
  have hget : (calldataFrame contract (adminAddressArguments arg value) ∅ evm).locals.get? arg =
      some (.address (AccountAddress.ofNat value.toNat)) := by
    change ((adminAddressArguments arg value).insert "__calldata"
      (.bytes evm.executionEnv.calldata)).get? arg = _
    rw [store_get_ne _ _ (by simpa using Ne.symm harg)]
    exact store_get_self _ _ _
  simp only [evalExpr?, hget, EvalResult.ofOption]

theorem adminAddressReverts (evm : EVM.State) (name arg event : Ident) (value : UInt256)
    (harg : arg ≠ "configurator") (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hno : ¬ adminAllowed evm) :
    ExecTransitionBody config contract evm (adminAddressArguments arg value)
      (adminAddressBody name arg event) .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  rw [evalAdminGuard evm rfl (by simp [calldataFrame, adminAddressArguments, harg]),
    decide_eq_false hno]

theorem adminAddressReturns (evm : EVM.State) (name arg event : Ident) (slot value : UInt256)
    (hcanon : value.toNat < EVM.addressModulus)
    (hnameData : name ≠ "__calldata") (hnameArg : name ≠ arg)
    (hargData : arg ≠ "__calldata") (hargAuth : arg ≠ "configurator")
    (hty : storageTypeAt? contract.storage { base := name } = some (.elem .address))
    (hloc : midnightStorageLayout { base := name } = some (.leaf (addressOffset0Loc slot)))
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : adminAllowed evm) (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody config contract evm (adminAddressArguments arg value)
      (adminAddressBody name arg event)
      (.returned (calldataFrame contract (adminAddressArguments arg value) ∅ evm)
        (addressUpdateState evm slot value) none) := by
  apply ExecFuncBody.execBlockOK
  apply guardedBodyBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · rw [evalAdminGuard evm rfl (by
      simp [calldataFrame, adminAddressArguments, hargAuth]), decide_eq_true hauth]
  apply ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm)
    (adminArgumentEval evm arg value hargData)
    (assignAddressVariable slot value hcanon (by
      simp [calldataFrame, adminAddressArguments, Ne.symm hnameData, Ne.symm hnameArg]) hty hloc))
  apply ExecBlock.consNormal
    (ExecStmt.emit (vals := [.address (AccountAddress.ofNat value.toNat)]) ?_ ?_) ExecBlock.nil
  · unfold addressUpdateState
    rw [storageStore_executionEnv]
    exact hperm
  · apply evalExprs?_singleton
    simpa only [evalExpr?] using adminArgumentEval evm arg value hargData

theorem adminAddressStatic (evm : EVM.State) (name arg event : Ident) (slot value : UInt256)
    (hcanon : value.toNat < EVM.addressModulus)
    (hnameData : name ≠ "__calldata") (hnameArg : name ≠ arg)
    (hargData : arg ≠ "__calldata") (hargAuth : arg ≠ "configurator")
    (hty : storageTypeAt? contract.storage { base := name } = some (.elem .address))
    (hloc : midnightStorageLayout { base := name } = some (.leaf (addressOffset0Loc slot)))
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : adminAllowed evm) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (adminAddressArguments arg value)
      (adminAddressBody name arg event) .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  apply guardedBodyBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · rw [evalAdminGuard evm rfl (by
      simp [calldataFrame, adminAddressArguments, hargAuth]), decide_eq_true hauth]
  apply ExecBlock.consStatic
  exact ExecStmt.assignStatic (adminArgumentEval evm arg value hargData)
    (assignAddressVariable slot value hcanon (by
      simp [calldataFrame, adminAddressArguments, Ne.symm hnameData, Ne.symm hnameArg]) hty hloc)
    hperm

end Benchmarks.Midnight

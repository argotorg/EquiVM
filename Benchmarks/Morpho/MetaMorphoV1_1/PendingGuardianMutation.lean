import Benchmarks.Morpho.MetaMorphoV1_1.PendingTimeStorage
import Benchmarks.Morpho.MetaMorphoV1_1.SetGuardianSource

/-! Source storage assignments for scheduling a guardian update. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def pendingTimeCastWord (data : UInt256) : UInt256 := UInt256.ofNat (data.toNat % 2 ^ 64)

theorem pendingTimeCastWord_toNat (data : UInt256) :
    (pendingTimeCastWord data).toNat = data.toNat % 2 ^ 64 := by
  exact UInt256.toNat_ofNat_of_lt (lt_trans (Nat.mod_lt _ (by decide)) (by decide))

theorem pendingTimeCastWord_store (old data : UInt256) :
    setPendingTimeWord old (pendingTimeCastWord data) = setPendingTimeWord old data := by
  simp only [setPendingTimeWord, pendingTimeCastWord_toNat, Nat.mod_mod]

theorem uint64CastSource {cfg : Config} {frame : Frame} {evm : EVM.State} {expr : Expr}
    {data : UInt256} (heval : evalExpr? cfg frame evm expr = .ok (uint256Value data)) :
    evalExpr? cfg frame evm (.cast expr (.elem (.int (.uint ⟨64, by decide⟩)))) =
      .ok (uint256Value (pendingTimeCastWord data)) := by
  simp only [evalExpr?, heval, bind, EvalResult.bind, castValue?, normalizeInt,
    uint256Value, EvalResult.ofOption, pendingTimeCastWord_toNat]
  norm_num [Int.natCast_mod, EVM.twoPow]

def pendingGuardianValueState (evm : EVM.State) (value : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨15⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨15⟩)
      (UInt256.ofNat value.val))

def pendingGuardianTimeState (evm : EVM.State) (time : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨15⟩
    (setPendingTimeWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨15⟩) time)

def pendingGuardianDelay (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨14⟩

def pendingGuardianTime (evm : EVM.State) : UInt256 :=
  UInt256.ofNat evm.executionEnv.header.timestamp + pendingGuardianDelay evm

abbrev pendingGuardianScheduleFits (evm : EVM.State) : Prop :=
  (UInt256.ofNat evm.executionEnv.header.timestamp).toNat +
    (pendingGuardianDelay evm).toNat < UInt256.size

def pendingGuardianScheduledState (evm : EVM.State) (value : AccountAddress) : EVM.State :=
  pendingGuardianTimeState (pendingGuardianValueState evm value) (pendingGuardianTime evm)

theorem assignPendingGuardianValue (evm : EVM.State) (locals imms : Store)
    (value : AccountAddress) (hbase : locals.get? "pendingGuardian" = none) :
    assignStorageRef? config ⟨contract, locals, imms⟩ evm .storage
      ⟨"pendingGuardian", [.field "value"]⟩ (.address value) =
      .ok (⟨contract, locals, imms⟩, pendingGuardianValueState evm value) := by
  apply assignStorageRef_storage_scalar_value
    (er := ⟨"pendingGuardian", [.field "value"]⟩) (ty := .elem .address) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bind, EvalResult.bind, pure]) rfl rfl rfl (.inl ⟨_, rfl⟩)
  have h := storageLocStore_address_offset0 evm ⟨15⟩ (UInt256.ofNat value.val)
    (addressWord_val_canonical value)
  have ha : AccountAddress.ofNat (UInt256.ofNat value.val).toNat = value :=
    accountAddress_of_word_val value
  rw [ha] at h
  exact h

theorem assignPendingGuardianTime (evm : EVM.State) (locals imms : Store) (time : UInt256)
    (hbase : locals.get? "pendingGuardian" = none) :
    assignStorageRef? config ⟨contract, locals, imms⟩ evm .storage
      ⟨"pendingGuardian", [.field "validAt"]⟩ (uint256Value (pendingTimeCastWord time)) =
      .ok (⟨contract, locals, imms⟩, pendingGuardianTimeState evm time) := by
  apply assignStorageRef_storage_scalar_value
    (er := ⟨"pendingGuardian", [.field "validAt"]⟩)
    (ty := .elem (.int (.uint ⟨64, by decide⟩))) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bind, EvalResult.bind, pure]) rfl rfl rfl (.inl ⟨_, rfl⟩)
  simpa only [pendingTimeCastWord_store] using
    storageLocStore_pendingTime evm ⟨15⟩ (pendingTimeCastWord time)

@[simp] theorem pendingGuardianValueState_executionEnv (evm : EVM.State)
    (value : AccountAddress) :
    (pendingGuardianValueState evm value).executionEnv = evm.executionEnv :=
  storageStore_executionEnv evm _ _ _

end Benchmarks.Morpho.MetaMorphoV1_1

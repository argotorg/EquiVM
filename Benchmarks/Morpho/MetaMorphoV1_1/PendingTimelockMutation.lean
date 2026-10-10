import Benchmarks.Morpho.MetaMorphoV1_1.PendingTimelockStorage
import Benchmarks.Morpho.MetaMorphoV1_1.SetTimelockSource

/-! Source storage assignments for scheduling a timelock update. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def pendingTimelockValueState (evm : EVM.State) (value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨17⟩
    (setPendingUint192Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨17⟩) value)

def pendingTimelockTimeState (evm : EVM.State) (time : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨17⟩
    (setPendingTimeHighWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨17⟩) time)

def pendingTimelockDelay (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨14⟩

def pendingTimelockTime (evm : EVM.State) : UInt256 :=
  UInt256.ofNat evm.executionEnv.header.timestamp + pendingTimelockDelay evm

abbrev pendingTimelockScheduleFits (evm : EVM.State) : Prop :=
  (UInt256.ofNat evm.executionEnv.header.timestamp).toNat +
    (pendingTimelockDelay evm).toNat < UInt256.size

def pendingTimelockScheduledState (evm : EVM.State) (value : UInt256) : EVM.State :=
  pendingTimelockTimeState (pendingTimelockValueState evm value) (pendingTimelockTime evm)

theorem assignPendingTimelockValue (evm : EVM.State) (locals imms : Store)
    (value : UInt256) (hbase : locals.get? "pendingTimelock" = none) :
    assignStorageRef? config ⟨contract, locals, imms⟩ evm .storage
      ⟨"pendingTimelock", [.field "value"]⟩ (uint256Value value) =
      .ok (⟨contract, locals, imms⟩, pendingTimelockValueState evm value) := by
  apply assignStorageRef_storage_scalar_value
    (er := ⟨"pendingTimelock", [.field "value"]⟩)
    (ty := .elem (.int (.uint ⟨192, by decide⟩))) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bind, EvalResult.bind, pure]) rfl rfl rfl (.inl ⟨_, rfl⟩)
  exact storageLocStore_pendingUint192 evm ⟨17⟩ value

theorem pendingTimeCastWord_storeHigh (old data : UInt256) :
    setPendingTimeHighWord old (pendingTimeCastWord data) =
      setPendingTimeHighWord old data := by
  simp only [setPendingTimeHighWord, pendingTimeCastWord_toNat, Nat.mod_mod]

theorem assignPendingTimelockTime (evm : EVM.State) (locals imms : Store) (time : UInt256)
    (hbase : locals.get? "pendingTimelock" = none) :
    assignStorageRef? config ⟨contract, locals, imms⟩ evm .storage
      ⟨"pendingTimelock", [.field "validAt"]⟩ (uint256Value (pendingTimeCastWord time)) =
      .ok (⟨contract, locals, imms⟩, pendingTimelockTimeState evm time) := by
  apply assignStorageRef_storage_scalar_value
    (er := ⟨"pendingTimelock", [.field "validAt"]⟩)
    (ty := .elem (.int (.uint ⟨64, by decide⟩))) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bind, EvalResult.bind, pure]) rfl rfl rfl (.inl ⟨_, rfl⟩)
  simpa only [pendingTimeCastWord_storeHigh] using
    storageLocStore_pendingTimeHigh evm ⟨17⟩ (pendingTimeCastWord time)

@[simp] theorem pendingTimelockValueState_executionEnv (evm : EVM.State) (value : UInt256) :
    (pendingTimelockValueState evm value).executionEnv = evm.executionEnv :=
  storageStore_executionEnv evm _ _ _

end Benchmarks.Morpho.MetaMorphoV1_1

import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalStorage

/-! The two packed pending-cap writes, including the captured scheduling timestamp. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def pendingCapValueState (evm : State) (id cap : UInt256) : State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (solcMappingSlot ⟨16⟩ id)
    (setPendingUint192Word
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨16⟩ id)) cap)

def pendingCapTimeState (evm : State) (id time : UInt256) : State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (solcMappingSlot ⟨16⟩ id)
    (setPendingTimeHighWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨16⟩ id)) time)

def pendingCapScheduledState (evm : State) (id cap : UInt256) : State :=
  pendingCapTimeState (pendingCapValueState evm id cap) id (pendingTimelockTime evm)

@[simp] theorem pendingCapValueState_env (evm : State) (id cap : UInt256) :
    (pendingCapValueState evm id cap).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

@[simp] theorem pendingCapTimeState_env (evm : State) (id time : UInt256) :
    (pendingCapTimeState evm id time).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

@[simp] theorem pendingCapScheduledState_env (evm : State) (id cap : UInt256) :
    (pendingCapScheduledState evm id cap).executionEnv = evm.executionEnv := by
  simp only [pendingCapScheduledState, pendingCapValueState_env, pendingCapTimeState_env]

theorem assignPendingCapValue {frame : Frame} {evm : State} {id : UInt256}
    (cap : UInt256) (hcontract : frame.contract = contract)
    (hbase : frame.locals.get? "pendingCap" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id)) :
    assignStorageRef? config frame evm .storage
      ⟨"pendingCap", [.mindex (.var "id"), .field "value"]⟩ (uint256Value cap) =
      .ok (frame, pendingCapValueState evm id cap) := by
  apply assignStorageRef_storage_scalar_value
    (er := ⟨"pendingCap", [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)),
      .field "value"]⟩)
    (ty := .elem (.int (.uint ⟨192, by decide⟩))) hbase
    (evalStorageRef_bytes32Field "pendingCap" "id" "value" _
      (word_toBytesBE_length_32 id) hid) (by rw [hcontract]; rfl) rfl
    (loc :=
      { slot := solcMappingSlot ⟨16⟩ id, offset := 0, size := 24, hbound := by decide,
        type := .int (.uint ⟨192, by decide⟩) })
  · change some (StorageAddr.leaf
      { slot := solcMappingSlot ⟨16⟩
          (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))),
        offset := 0, size := 24, hbound := by decide,
        type := .int (.uint ⟨192, by decide⟩) }) = _
    rw [show keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)) = id from
      keyValueToWord_fixedBytes32 id]
  · exact .inl ⟨_, rfl⟩
  · exact storageLocStore_pendingUint192 evm (solcMappingSlot ⟨16⟩ id) cap

theorem assignPendingCapTime {frame : Frame} {evm : State} {id : UInt256}
    (time : UInt256) (hcontract : frame.contract = contract)
    (hbase : frame.locals.get? "pendingCap" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id)) :
    assignStorageRef? config frame evm .storage
      ⟨"pendingCap", [.mindex (.var "id"), .field "validAt"]⟩
      (uint256Value (pendingTimeCastWord time)) =
      .ok (frame, pendingCapTimeState evm id time) := by
  apply assignStorageRef_storage_scalar_value
    (er := ⟨"pendingCap", [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)),
      .field "validAt"]⟩)
    (ty := .elem (.int (.uint ⟨64, by decide⟩))) hbase
    (evalStorageRef_bytes32Field "pendingCap" "id" "validAt" _
      (word_toBytesBE_length_32 id) hid) (by rw [hcontract]; rfl) rfl
    (loc :=
      { slot := solcMappingSlot ⟨16⟩ id, offset := 24, size := 8, hbound := by decide,
        type := .int (.uint ⟨64, by decide⟩) })
  · change some (StorageAddr.leaf
      { slot := solcMappingSlot ⟨16⟩
          (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))),
        offset := 24, size := 8, hbound := by decide,
        type := .int (.uint ⟨64, by decide⟩) }) = _
    rw [show keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)) = id from
      keyValueToWord_fixedBytes32 id]
  · exact .inl ⟨_, rfl⟩
  · simpa only [pendingTimeCastWord_storeHigh] using
      storageLocStore_pendingTimeHigh evm (solcMappingSlot ⟨16⟩ id) (pendingTimeCastWord time)

end Benchmarks.Morpho.MetaMorphoV1_1

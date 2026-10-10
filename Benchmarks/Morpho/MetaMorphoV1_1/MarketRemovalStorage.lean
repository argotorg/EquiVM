import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositQueueSource
import Benchmarks.Morpho.MetaMorphoV1_1.PendingTimelockMutation

/-! Packed cap, enablement, and timestamp fields used when scheduling market removal. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000

def marketRemovalConfigWord (evm : State) (id : UInt256) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨13⟩ id)

def marketRemovalRemovableAt (evm : State) (id : UInt256) : UInt256 :=
  UInt256.shiftRight (marketRemovalConfigWord evm id) ⟨192⟩

def marketRemovalCap (evm : State) (id : UInt256) : UInt256 :=
  UInt256.land (marketRemovalConfigWord evm id) (UInt256.ofNat (2 ^ 184 - 1))

def marketRemovalEnabledWord (evm : State) (id : UInt256) : UInt256 :=
  UInt256.land (UInt256.shiftRight (marketRemovalConfigWord evm id) ⟨184⟩) ⟨255⟩

def marketRemovalPendingAt (evm : State) (id : UInt256) : UInt256 :=
  UInt256.shiftRight
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨16⟩ id)) ⟨192⟩

abbrev marketRemovalAllowed (evm : State) (id : UInt256) : Prop :=
  marketRemovalRemovableAt evm id = ⟨0⟩ ∧ marketRemovalCap evm id = ⟨0⟩ ∧
    marketRemovalEnabledWord evm id ≠ ⟨0⟩ ∧ marketRemovalPendingAt evm id = ⟨0⟩

theorem marketRemovalTimeRead (pending : Bool) {frame : Frame} {evm : State} {id : UInt256}
    (hcontract : frame.contract = contract)
    (hbase : frame.locals.get? (if pending then "pendingCap" else "config") = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id)) :
    evalExpr? config frame evm
      (.storage ⟨if pending then "pendingCap" else "config", [.mindex (.var "id"),
        .field (if pending then "validAt" else "removableAt")]⟩) =
      .ok (uint256Value (if pending then marketRemovalPendingAt evm id
        else marketRemovalRemovableAt evm id)) := by
  cases pending with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hbase ⊢
      apply evalExpr_storage_scalar_value
        (er := ⟨"config", [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)),
          .field "removableAt"]⟩)
        (t := .int (.uint ⟨64, by decide⟩)) hbase
        (evalStorageRef_bytes32Field "config" "id" "removableAt" _
          (word_toBytesBE_length_32 id) hid) (by rw [hcontract]; rfl) rfl
        (loc :=
          { slot := solcMappingSlot ⟨13⟩ id, offset := 24, size := 8,
            hbound := by decide, type := .int (.uint ⟨64, by decide⟩) })
      · change some (StorageAddr.leaf
          { slot := solcMappingSlot ⟨13⟩
              (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))),
            offset := 24, size := 8, hbound := by decide,
            type := .int (.uint ⟨64, by decide⟩) }) = _
        rw [show keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)) = id from
          keyValueToWord_fixedBytes32 id]
      · exact storageLocLoad_uint_high evm (solcMappingSlot ⟨13⟩ id)
          24 8 ⟨64, by decide⟩ rfl rfl
  | true =>
      simp only [if_true] at hbase ⊢
      apply evalExpr_storage_scalar_value
        (er := ⟨"pendingCap", [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)),
          .field "validAt"]⟩)
        (t := .int (.uint ⟨64, by decide⟩)) hbase
        (evalStorageRef_bytes32Field "pendingCap" "id" "validAt" _
          (word_toBytesBE_length_32 id) hid) (by rw [hcontract]; rfl) rfl
        (loc :=
          { slot := solcMappingSlot ⟨16⟩ id, offset := 24, size := 8,
            hbound := by decide, type := .int (.uint ⟨64, by decide⟩) })
      · change some (StorageAddr.leaf
          { slot := solcMappingSlot ⟨16⟩
              (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))),
            offset := 24, size := 8, hbound := by decide,
            type := .int (.uint ⟨64, by decide⟩) }) = _
        rw [show keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)) = id from
          keyValueToWord_fixedBytes32 id]
      · exact storageLocLoad_uint_high evm (solcMappingSlot ⟨16⟩ id)
          24 8 ⟨64, by decide⟩ rfl rfl

theorem marketRemovalEnabledRead {frame : Frame} {evm : State} {id : UInt256}
    (hcontract : frame.contract = contract) (hbase : frame.locals.get? "config" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id)) :
    evalExpr? config frame evm
      (.storage ⟨"config", [.mindex (.var "id"), .field "enabled"]⟩) =
      .ok (.bool (decide (marketRemovalEnabledWord evm id ≠ ⟨0⟩))) := by
  apply evalExpr_storage_scalar_value
    (er := ⟨"config", [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)),
      .field "enabled"]⟩)
    (t := .bool) hbase
    (evalStorageRef_bytes32Field "config" "id" "enabled" _
      (word_toBytesBE_length_32 id) hid) (by rw [hcontract]; rfl) rfl
    (loc :=
      { slot := solcMappingSlot ⟨13⟩ id, offset := 23, size := 1,
        hbound := by decide, type := .bool })
  · change some (StorageAddr.leaf
      { slot := solcMappingSlot ⟨13⟩
          (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))),
        offset := 23, size := 1, hbound := by decide, type := .bool }) = _
    rw [show keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)) = id from
      keyValueToWord_fixedBytes32 id]
  · rw [storageLocLoad_bool_shift]
    change wordToElem .bool (marketRemovalEnabledWord evm id) = _
    rw [wordToElemBool, decide_not]

def marketRemovalTimeState (evm : State) (id time : UInt256) : State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (solcMappingSlot ⟨13⟩ id)
    (setPendingTimeHighWord (marketRemovalConfigWord evm id) time)

theorem assignMarketRemovalTime {frame : Frame} {evm : State} {id : UInt256}
    (time : UInt256) (hcontract : frame.contract = contract)
    (hbase : frame.locals.get? "config" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id)) :
    assignStorageRef? config frame evm .storage
      ⟨"config", [.mindex (.var "id"), .field "removableAt"]⟩
      (uint256Value (pendingTimeCastWord time)) =
        .ok (frame, marketRemovalTimeState evm id time) := by
  apply assignStorageRef_storage_scalar_value
    (er := ⟨"config", [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)),
      .field "removableAt"]⟩)
    (ty := .elem (.int (.uint ⟨64, by decide⟩))) hbase
    (evalStorageRef_bytes32Field "config" "id" "removableAt" _
      (word_toBytesBE_length_32 id) hid) (by rw [hcontract]; rfl) rfl
    (loc :=
      { slot := solcMappingSlot ⟨13⟩ id, offset := 24, size := 8,
        hbound := by decide, type := .int (.uint ⟨64, by decide⟩) })
  · change some (StorageAddr.leaf
      { slot := solcMappingSlot ⟨13⟩
          (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))),
        offset := 24, size := 8, hbound := by decide,
        type := .int (.uint ⟨64, by decide⟩) }) = _
    rw [show keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)) = id from
      keyValueToWord_fixedBytes32 id]
  · exact .inl ⟨_, rfl⟩
  · simpa only [pendingTimeCastWord_storeHigh] using
      storageLocStore_pendingTimeHigh evm (solcMappingSlot ⟨13⟩ id) (pendingTimeCastWord time)

end Benchmarks.Morpho.MetaMorphoV1_1

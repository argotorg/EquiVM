import Benchmarks.Morpho.MetaMorphoV1_1.BodyCommon
import Reasoning.Storage

/-! Storage reads at the physical slots of the compiled contract. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

theorem evalStorage_lostAssets (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "lostAssets" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"lostAssets", []⟩) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨23⟩).toNat)) := by
  exact evalExpr_storage_scalar_value (er := ⟨"lostAssets", []⟩)
    (t := .int (.uint ⟨256, by decide⟩)) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (show storageTypeAt? contract.storage ⟨"lostAssets", []⟩ =
      some (.elem (.int (.uint ⟨256, by decide⟩))) from by decide +kernel)
    rfl rfl (storageLocLoad_uint256 evm ⟨23⟩)

theorem evalStorage_lastTotalAssets (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "lastTotalAssets" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"lastTotalAssets", []⟩) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨22⟩).toNat)) := by
  exact evalExpr_storage_scalar_value (er := ⟨"lastTotalAssets", []⟩)
    (t := .int (.uint ⟨256, by decide⟩)) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (show storageTypeAt? contract.storage ⟨"lastTotalAssets", []⟩ =
      some (.elem (.int (.uint ⟨256, by decide⟩))) from by decide +kernel)
    rfl rfl (storageLocLoad_uint256 evm ⟨22⟩)

theorem evalStorage_timelock (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "timelock" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"timelock", []⟩) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨14⟩).toNat)) := by
  exact evalExpr_storage_scalar_value (er := ⟨"timelock", []⟩)
    (t := .int (.uint ⟨256, by decide⟩)) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (show storageTypeAt? contract.storage ⟨"timelock", []⟩ =
      some (.elem (.int (.uint ⟨256, by decide⟩))) from by decide +kernel)
    rfl rfl (storageLocLoad_uint256 evm ⟨14⟩)

theorem evalStorage_totalSupply (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "_totalSupply" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"_totalSupply", []⟩) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)) := by
  exact evalExpr_storage_scalar_value (er := ⟨"_totalSupply", []⟩)
    (t := .int (.uint ⟨256, by decide⟩)) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (show storageTypeAt? contract.storage ⟨"_totalSupply", []⟩ =
      some (.elem (.int (.uint ⟨256, by decide⟩))) from by decide +kernel)
    rfl rfl (storageLocLoad_uint256 evm ⟨2⟩)

theorem evalStorage_curator (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "curator" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"curator", []⟩) =
      .ok (.address (AccountAddress.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩) solcAddrMask).toNat)) := by
  exact evalExpr_storage_scalar_value (er := ⟨"curator", []⟩) (t := .address) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (show storageTypeAt? contract.storage ⟨"curator", []⟩ = some (.elem .address)
      from by decide +kernel)
    rfl rfl (storageLocLoad_address_offset0 evm ⟨10⟩)

theorem evalStorage_guardian (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "guardian" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"guardian", []⟩) =
      .ok (.address (AccountAddress.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩) solcAddrMask).toNat)) := by
  exact evalExpr_storage_scalar_value (er := ⟨"guardian", []⟩) (t := .address) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (show storageTypeAt? contract.storage ⟨"guardian", []⟩ = some (.elem .address)
      from by decide +kernel)
    rfl rfl (storageLocLoad_address_offset0 evm ⟨12⟩)

theorem evalStorage_skimRecipient (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "skimRecipient" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"skimRecipient", []⟩) =
      .ok (.address (AccountAddress.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨19⟩) solcAddrMask).toNat)) := by
  exact evalExpr_storage_scalar_value (er := ⟨"skimRecipient", []⟩) (t := .address) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (show storageTypeAt? contract.storage ⟨"skimRecipient", []⟩ = some (.elem .address)
      from by decide +kernel)
    rfl rfl (storageLocLoad_address_offset0 evm ⟨19⟩)

theorem evalStorage_owner (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "_owner" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"_owner", []⟩) =
      .ok (.address (AccountAddress.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩) solcAddrMask).toNat)) := by
  exact evalExpr_storage_scalar_value (er := ⟨"_owner", []⟩) (t := .address) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (show storageTypeAt? contract.storage ⟨"_owner", []⟩ = some (.elem .address)
      from by decide +kernel)
    rfl rfl (storageLocLoad_address_offset0 evm ⟨8⟩)

theorem evalStorage_pendingOwner (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "_pendingOwner" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"_pendingOwner", []⟩) =
      .ok (.address (AccountAddress.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩) solcAddrMask).toNat)) := by
  exact evalExpr_storage_scalar_value (er := ⟨"_pendingOwner", []⟩) (t := .address) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (show storageTypeAt? contract.storage ⟨"_pendingOwner", []⟩ = some (.elem .address)
      from by decide +kernel)
    rfl rfl (storageLocLoad_address_offset0 evm ⟨9⟩)

-- LIBRARY CANDIDATE: load an address occupying the high twenty bytes of a storage slot.
theorem storageLocLoad_highAddress (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm
      { slot := slot, offset := 12, size := 20, hbound := by decide, type := .address } =
      .address (AccountAddress.ofNat
        (UInt256.shiftRight (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          ⟨96⟩).toNat) := by
  unfold storageLocLoad wordToElem
  change Value.address (AccountAddress.ofNat
      (fromBytes' ((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract 12 32))) = _
  rw [List.extract_eq_take_drop, List.take_of_length_le (by
    rw [List.length_drop, (EVM.Word.toBytesLEWithSizeProof _).2]), fromBytes'_drop_wordLE]
  exact congrArg (fun n ↦ Value.address (AccountAddress.ofNat n))
    (wordShiftRight_toNat _ 96 (by decide)).symm

theorem evalStorage_fee (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "fee" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"fee", []⟩) =
      .ok (.int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨18⟩)
        (UInt256.ofNat (2 ^ 96 - 1))).toNat)) := by
  exact evalExpr_storage_scalar_value (er := ⟨"fee", []⟩)
    (t := .int (.uint ⟨96, by decide⟩)) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (show storageTypeAt? contract.storage ⟨"fee", []⟩ =
      some (.elem (.int (.uint ⟨96, by decide⟩))) from by decide +kernel)
    rfl rfl (storageLocLoad_uint_offset0 evm ⟨18⟩ 12 ⟨96, by decide⟩ rfl (by decide))

theorem evalStorage_feeRecipient (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "feeRecipient" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"feeRecipient", []⟩) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.shiftRight (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨18⟩)
          ⟨96⟩).toNat)) := by
  exact evalExpr_storage_scalar_value (er := ⟨"feeRecipient", []⟩) (t := .address) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (show storageTypeAt? contract.storage ⟨"feeRecipient", []⟩ = some (.elem .address)
      from by decide +kernel)
    rfl rfl (storageLocLoad_highAddress evm ⟨18⟩)

-- LIBRARY CANDIDATE: evaluate a dynamic storage array's length through its anchor slot.
theorem storageDynamicArrayLength {cfg : Config} {layout : StorageLayout}
    {evm : EVM.State} {er : EvaledStorageRef} {elem : StorageType} {slot : UInt256}
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hanchor : layout er = some (.anchor slot)) :
    cfg.storageBackend.length er (.dynamicArray elem) evm =
      .ok (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat := by
  rw [hbackend]
  simp only [solidityStorageBackend, solidityStorageLength?, solidityDynamicLength?,
    solidityLengthLoc?, solidityAnchor?_of_anchor hanchor, Option.map_some,
    EvalResult.ofOption, bind, EvalResult.bind]
  have hload := storageLocLoad_uint256 evm slot
  change storageLocLoad evm (solidityAnchorWordLoc slot) = _ at hload
  rw [hload]
  simp only [Int.ofNat_eq_natCast]
  rw [if_neg (not_lt_of_ge (Int.natCast_nonneg _))]
  rfl

-- LIBRARY CANDIDATE: evaluate a dynamic storage array's length through its anchor slot.
theorem evalStorageDynamicArrayLength {cfg : Config} {layout : StorageLayout}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {elem : StorageType} {slot : UInt256}
    (hbase : solm.locals.get? ref.base = none)
    (her : evalStorageRef cfg solm evm ref = .ok er)
    (hty : storageTypeAt? solm.contract.storage er = some (.dynamicArray elem))
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hanchor : layout er = some (.anchor slot)) :
    evalExpr? cfg solm evm (.arrayLength .storage ref) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat)) := by
  rw [evalExpr?]
  simp only [resolveStorageRef?_ok hbase her hty, bind, EvalResult.bind]
  rw [storageDynamicArrayLength hbackend hanchor]
  rfl

theorem evalStorage_supplyQueueLength (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "supplyQueue" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.arrayLength .storage ⟨"supplyQueue", []⟩) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨20⟩).toNat)) := by
  exact evalStorageDynamicArrayLength (er := ⟨"supplyQueue", []⟩)
    (elem := .elem (.bytes ⟨31, by decide⟩)) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (show storageTypeAt? contract.storage ⟨"supplyQueue", []⟩ =
      some (.dynamicArray (.elem (.bytes ⟨31, by decide⟩))) from by decide +kernel) rfl rfl

theorem evalStorage_withdrawQueueLength (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "withdrawQueue" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.arrayLength .storage ⟨"withdrawQueue", []⟩) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨21⟩).toNat)) := by
  exact evalStorageDynamicArrayLength (er := ⟨"withdrawQueue", []⟩)
    (elem := .elem (.bytes ⟨31, by decide⟩)) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (show storageTypeAt? contract.storage ⟨"withdrawQueue", []⟩ =
      some (.dynamicArray (.elem (.bytes ⟨31, by decide⟩))) from by decide +kernel) rfl rfl

end Benchmarks.Morpho.MetaMorphoV1_1

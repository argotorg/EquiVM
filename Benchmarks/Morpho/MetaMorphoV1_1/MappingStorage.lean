import Benchmarks.Morpho.MetaMorphoV1_1.Storage

/-! Mapping reads and scratch-memory facts shared by the mapping getters. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: resolve one address-valued mapping index held in a local variable.
theorem evalStorageRef_addressIndex {cfg : Config} {solm : Frame} {evm : EVM.State}
    (base name : Ident) (addr : AccountAddress)
    (hget : solm.locals.get? name = some (.address addr)) :
    evalStorageRef cfg solm evm ⟨base, [.mindex (.var name)]⟩ =
      .ok ⟨base, [.mindex (.address addr)]⟩ := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hget,
    valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem evalStorage_balanceOf (evm : EVM.State) (locals imms : Store) (w : UInt256)
    (hbase : locals.get? "_balances" = none)
    (hget : locals.get? "account" = some (.address (AccountAddress.ofNat w.toNat)))
    (hcanon : w.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"_balances", [.mindex (.var "account")]⟩) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (solcMappingSlot ⟨0⟩ w)).toNat)) := by
  apply evalExpr_storage_scalar_value
    (er := ⟨"_balances", [.mindex (.address (AccountAddress.ofNat w.toNat))]⟩)
    (t := .int (.uint ⟨256, by decide⟩)) hbase
    (evalStorageRef_addressIndex "_balances" "account" _ hget) rfl rfl
    (loc := uint256Loc (solcMappingSlot ⟨0⟩ w))
  · change some (StorageAddr.leaf (uint256Loc
      (solcMappingSlot ⟨0⟩ (keyValueToWord (.address (AccountAddress.ofNat w.toNat)))))) = _
    rw [keyValueToWord_address_of_canonical w hcanon]
  · exact storageLocLoad_uint256 evm _

theorem evalStorage_nonces (evm : EVM.State) (locals imms : Store) (w : UInt256)
    (hbase : locals.get? "_nonces" = none)
    (hget : locals.get? "owner" = some (.address (AccountAddress.ofNat w.toNat)))
    (hcanon : w.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"_nonces", [.mindex (.var "owner")]⟩) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (solcMappingSlot ⟨7⟩ w)).toNat)) := by
  apply evalExpr_storage_scalar_value
    (er := ⟨"_nonces", [.mindex (.address (AccountAddress.ofNat w.toNat))]⟩)
    (t := .int (.uint ⟨256, by decide⟩)) hbase
    (evalStorageRef_addressIndex "_nonces" "owner" _ hget) rfl rfl
    (loc := uint256Loc (solcMappingSlot ⟨7⟩ w))
  · change some (StorageAddr.leaf (uint256Loc
      (solcMappingSlot ⟨7⟩ (keyValueToWord (.address (AccountAddress.ofNat w.toNat)))))) = _
    rw [keyValueToWord_address_of_canonical w hcanon]
  · exact storageLocLoad_uint256 evm _

theorem evalStorage_isAllocator (evm : EVM.State) (locals imms : Store) (w : UInt256)
    (hbase : locals.get? "isAllocator" = none)
    (hget : locals.get? "arg0" = some (.address (AccountAddress.ofNat w.toNat)))
    (hcanon : w.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"isAllocator", [.mindex (.var "arg0")]⟩) =
      .ok (wordToElem .bool (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨11⟩ w))
        ⟨255⟩)) := by
  apply evalExpr_storage_scalar_value
    (er := ⟨"isAllocator", [.mindex (.address (AccountAddress.ofNat w.toNat))]⟩)
    (t := .bool) hbase
    (evalStorageRef_addressIndex "isAllocator" "arg0" _ hget) rfl rfl
    (loc := boolOffset0Loc (solcMappingSlot ⟨11⟩ w))
  · change some (StorageAddr.leaf (boolOffset0Loc
      (solcMappingSlot ⟨11⟩ (keyValueToWord (.address (AccountAddress.ofNat w.toNat)))))) = _
    rw [keyValueToWord_address_of_canonical w hcanon]
  · exact storageLocLoad_bool_offset0 evm _

-- LIBRARY CANDIDATE: return a word after writes to the initial scratch-memory region.
theorem returnScratchWordMemory (mem : ByteArray) (w : UInt256)
    (hsize : mem.size = 96) (hread : mem.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray) :
    (w.toByteArray.write 0 mem (memLoad ⟨64⟩ mem).toNat 32).readWithPadding
      (memLoad ⟨64⟩ mem).toNat 32 = w.toByteArray := by
  have hptr : memLoad ⟨64⟩ mem = ⟨128⟩ :=
    mloadFreePtrValue (by omega) hread
  rw [hptr]
  exact solcScratchReturnMem_read128 w hsize

theorem mappingScratchReturnMemory (key slot value : UInt256) :
    (value.toByteArray.write 0 (twoWordHashMem key slot solcFreePtrMem)
      (memLoad ⟨64⟩ (twoWordHashMem key slot solcFreePtrMem)).toNat 32).readWithPadding
      (memLoad ⟨64⟩ (twoWordHashMem key slot solcFreePtrMem)).toNat 32 = value.toByteArray :=
  returnScratchWordMemory _ value (twoWordHashMem_size_96 key slot solcFreePtrMem_size)
    (twoWordHashMem_read64 key slot solcFreePtrMem_size solcFreePtrMem_read64)

theorem mappingScratchHash (key slot : UInt256) :
    keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem key slot solcFreePtrMem) = solcMappingSlot slot key :=
  twoWordHashMem_solcMappingSlot slot key solcFreePtrMem_size

theorem mappingScratch_mload64 (key slot : UInt256) :
    memLoad ⟨64⟩ (twoWordHashMem key slot solcFreePtrMem) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [twoWordHashMem_size_96 key slot solcFreePtrMem_size]; decide)
    (twoWordHashMem_read64 key slot solcFreePtrMem_size solcFreePtrMem_read64)

end Benchmarks.Morpho.MetaMorphoV1_1

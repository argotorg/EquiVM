import Benchmarks.Morpho.MetaMorphoV1_1.MappingStorage

/-! Nested address mapping reads and their two keccak memory regions. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- GENERALIZES evalStorageRef_addressIndex to a pair of address mapping indices.
theorem evalStorageRef_twoAddressIndices {cfg : Config} {solm : Frame} {evm : EVM.State}
    (base name₁ name₂ : Ident) (a b : AccountAddress)
    (hget₁ : solm.locals.get? name₁ = some (.address a))
    (hget₂ : solm.locals.get? name₂ = some (.address b)) :
    evalStorageRef cfg solm evm ⟨base, [.mindex (.var name₁), .mindex (.var name₂)]⟩ =
      .ok ⟨base, [.mindex (.address a), .mindex (.address b)]⟩ := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hget₁, hget₂,
    valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem evalStorage_allowance (evm : EVM.State) (locals imms : Store) (owner spender : UInt256)
    (hbase : locals.get? "_allowances" = none)
    (howner : locals.get? "owner" = some (.address (AccountAddress.ofNat owner.toNat)))
    (hspender : locals.get? "spender" = some (.address (AccountAddress.ofNat spender.toNat)))
    (hcanon₁ : owner.toNat < EVM.addressModulus) (hcanon₂ : spender.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"_allowances", [.mindex (.var "owner"), .mindex (.var "spender")]⟩) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (solcMappingSlot (solcMappingSlot ⟨1⟩ owner) spender)).toNat)) := by
  apply evalExpr_storage_scalar_value
    (er := ⟨"_allowances", [.mindex (.address (AccountAddress.ofNat owner.toNat)),
      .mindex (.address (AccountAddress.ofNat spender.toNat))]⟩)
    (t := .int (.uint ⟨256, by decide⟩)) hbase
    (evalStorageRef_twoAddressIndices "_allowances" "owner" "spender" _ _ howner hspender)
    rfl rfl (loc := uint256Loc (solcMappingSlot (solcMappingSlot ⟨1⟩ owner) spender))
  · change some (StorageAddr.leaf (uint256Loc
      (solcMappingSlot
        (solcMappingSlot ⟨1⟩ (keyValueToWord (.address (AccountAddress.ofNat owner.toNat))))
        (keyValueToWord (.address (AccountAddress.ofNat spender.toNat)))))) = _
    rw [keyValueToWord_address_of_canonical owner hcanon₁,
      keyValueToWord_address_of_canonical spender hcanon₂]
  · exact storageLocLoad_uint256 evm _

-- GENERALIZES mappingScratchReturnMemory to a previously used scratch-memory region.
theorem twoWordScratchReturnMemory (mem : ByteArray) (key slot value : UInt256)
    (hsize : mem.size = 96) (hread : mem.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray) :
    (value.toByteArray.write 0 (twoWordHashMem key slot mem)
      (memLoad ⟨64⟩ (twoWordHashMem key slot mem)).toNat 32).readWithPadding
      (memLoad ⟨64⟩ (twoWordHashMem key slot mem)).toNat 32 = value.toByteArray :=
  returnScratchWordMemory _ value (twoWordHashMem_size_96 key slot hsize)
    (twoWordHashMem_read64 key slot hsize hread)

theorem nestedMappingReturnMemory (first second slot value : UInt256) :
    (value.toByteArray.write 0
      (twoWordHashMem second
        (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem first slot solcFreePtrMem))
        (twoWordHashMem first slot solcFreePtrMem))
      (memLoad ⟨64⟩ (twoWordHashMem second
        (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem first slot solcFreePtrMem))
        (twoWordHashMem first slot solcFreePtrMem))).toNat 32).readWithPadding
      (memLoad ⟨64⟩ (twoWordHashMem second
        (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem first slot solcFreePtrMem))
        (twoWordHashMem first slot solcFreePtrMem))).toNat 32 = value.toByteArray :=
  twoWordScratchReturnMemory _ second _ value
    (twoWordHashMem_size_96 first slot solcFreePtrMem_size)
    (twoWordHashMem_read64 first slot solcFreePtrMem_size solcFreePtrMem_read64)

theorem nestedMappingHash (first second slot : UInt256) :
    keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem second
      (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem first slot solcFreePtrMem))
      (twoWordHashMem first slot solcFreePtrMem)) =
        solcMappingSlot (solcMappingSlot slot first) second := by
  have houter : keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem second
      (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem first slot solcFreePtrMem))
      (twoWordHashMem first slot solcFreePtrMem)) =
      solcMappingSlot (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem first slot solcFreePtrMem)) second :=
    twoWordHashMem_solcMappingSlot _ second
      (twoWordHashMem_size_96 first slot solcFreePtrMem_size)
  rw [houter, mappingScratchHash]

end Benchmarks.Morpho.MetaMorphoV1_1

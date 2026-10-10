import Benchmarks.Morpho.MetaMorphoV1_1.ArrayStorage
import Benchmarks.Morpho.MetaMorphoV1_1.StringStorageSource

/-! A dynamic bytes32 array grows by writing its length and then its new element. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: pushing a full-slot word through an arbitrary Solidity locator.
theorem solidityPushWordArray {layout : StorageLayout} {er : EvaledStorageRef}
    {header data : UInt256} (evm : State) (len word : UInt256)
    (hlen : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner header = len)
    (hanchor : layout er = some (.anchor header))
    (hloc : layout { er with steps := er.steps ++ [.aindex (.int (Int.ofNat len.toNat))] } =
      some (.leaf (bytes32Loc data))) :
    solidityPushStorage? layout er (.dynamicArray (.elem (.bytes abiBytes32Width)))
      (some (wordBytes32Value word)) evm =
      .ok (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner header (len + ⟨1⟩))
        evm.executionEnv.codeOwner data word) := by
  have hl : solidityDynamicLength? layout evm er = .ok len.toNat := by
    simpa only [hlen] using storageDynamicArrayLength
      (cfg :=
        { storageBackend := solidityStorageBackend layout,
          externalABI := ⟨fun _ _ ↦ none, fun _ _ ↦ none⟩,
          selfDeployment := fun _ _ ↦ none })
      (elem := .elem (.bytes abiBytes32Width)) (evm := evm) rfl hanchor
  simp only [solidityPushStorage?, hl, bind, EvalResult.bind, solidityLengthLoc?,
    solidityAnchor?_of_anchor hanchor, Option.map_some, EvalResult.ofOption]
  have hs : storageLocStore evm (solidityAnchorWordLoc header) (.int (↑len.toNat + 1)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner header (len + ⟨1⟩)) :=
    storageLocStore_uint256_succ evm header len
  rw [hs]
  have he : layout { er with steps := er.steps ++ [.aindex (.int (len.toNat : Int))] } =
      some (.leaf (bytes32Loc data)) := hloc
  simp only [EvalResult.ofOption, bind, EvalResult.bind, solidityWriteStorage?,
    solidityLeafLoc?_of_leaf he]
  rw [storageLocStore_bytes32 _ _ word (wordBytes32Value word) (valueToWord_bytes32_word word)]
  simp only [storageStore_executionEnv]

-- LIBRARY CANDIDATE: normalize the full-slot array index emitted by the Solidity locator.
theorem bytes32ArrayIndexLoc (base : UInt256) (i : Nat) :
    ({ slot := base + UInt256.ofNat ((keyValueToWord (.int (Int.ofNat i))).toNat / 1)
       offset := Fin.ofNat 32 ((keyValueToWord (.int (Int.ofNat i))).toNat % 1 * 32)
       size := 32, hbound := by simp, type := .bytes ⟨31, by decide⟩ } : StorageLoc) =
      bytes32Loc (base + UInt256.ofNat i) := by
  simp only [keyValueToWord, wordOfInt_ofNat_toNat_gen, Nat.div_one, Nat.mod_one,
    Nat.zero_mul, u256_ofNat_toNat]
  rfl

theorem withdrawQueueElementLayout (i : Nat) :
    stringStorageLayout ⟨"withdrawQueue", [.aindex (.int (Int.ofNat i))]⟩ =
      some (.leaf (bytes32Loc (solidityBytesDataBaseSlot ⟨21⟩ + UInt256.ofNat i))) := by
  change some (StorageAddr.leaf
    { slot := solidityBytesDataBaseSlot ⟨21⟩ +
        UInt256.ofNat ((keyValueToWord (.int (Int.ofNat i))).toNat / 1)
      offset := Fin.ofNat 32 ((keyValueToWord (.int (Int.ofNat i))).toNat % 1 * 32)
      size := 32, hbound := by simp, type := .bytes ⟨31, by decide⟩ }) = _
  rw [bytes32ArrayIndexLoc]

end Benchmarks.Morpho.MetaMorphoV1_1

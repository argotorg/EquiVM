import Benchmarks.CompoundIII.Comet.ConstructorDecodeUint64
import Benchmarks.CompoundIII.Comet.CreationBlocks_002

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometConstructorDecodeUint104 {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig}
    {aw : UInt256} {k C : Nat}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨462⟩
      [constructorRecordWord c 16, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
      (constructorScalarMemory c 16) aw ByteArray.empty σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨531⟩
      [constructorRecordWord c 19, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
      (constructorScalarMemory c 19) aw' ByteArray.empty σ k' C' := by
  have s17 := cometWithExtendedAssetListCreation_block_462 (by change 8 ≤ 1024; decide)
    (by native_decide) h
  have hm17 : cometWithExtendedAssetListCreation_block_462_memory
      (mem := constructorScalarMemory c 16) (x0 := constructorRecordWord c 16)
      (x4 := UInt256.ofNat (constructorRecordBase c)) = constructorScalarMemory c 17 := by
    unfold cometWithExtendedAssetListCreation_block_462_memory
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    rfl
  rw [hm17] at s17
  change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
    (initState σ σ₀ g A I)
    ⟨2789⟩ [UInt256.ofNat 1504, ⟨485⟩, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
    (constructorScalarMemory c 17) _ ByteArray.empty σ _ _ at s17
  obtain ⟨_, _, _, r17⟩ := cometCreationReadUint104 (by change 9 ≤ 1024; decide)
    (constructorScalarMemory_loadScalar c 17 17 (by decide) hsize)
    (show (constructorRecordWord c 17).toNat < 2^104 from
      constructorUintScalar_canonical ⟨104, by decide⟩ c.baseMinForRewards)
    (by native_decide) s17
  have s18 := cometWithExtendedAssetListCreation_block_485 (by change 8 ≤ 1024; decide)
    (by native_decide) r17
  have hm18 : cometWithExtendedAssetListCreation_block_485_memory
      (mem := constructorScalarMemory c 17) (x0 := constructorRecordWord c 17)
      (x4 := UInt256.ofNat (constructorRecordBase c)) = constructorScalarMemory c 18 := by
    unfold cometWithExtendedAssetListCreation_block_485_memory
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    rfl
  rw [hm18] at s18
  change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
    (initState σ σ₀ g A I)
    ⟨2789⟩ [UInt256.ofNat 1536, ⟨508⟩, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
    (constructorScalarMemory c 18) _ ByteArray.empty σ _ _ at s18
  obtain ⟨_, _, _, r18⟩ := cometCreationReadUint104 (by change 9 ≤ 1024; decide)
    (constructorScalarMemory_loadScalar c 18 18 (by decide) hsize)
    (show (constructorRecordWord c 18).toNat < 2^104 from
      constructorUintScalar_canonical ⟨104, by decide⟩ c.baseBorrowMin)
    (by native_decide) s18
  have s19 := cometWithExtendedAssetListCreation_block_508 (by change 8 ≤ 1024; decide)
    (by native_decide) r18
  have hm19 : cometWithExtendedAssetListCreation_block_508_memory
      (mem := constructorScalarMemory c 18) (x0 := constructorRecordWord c 18)
      (x4 := UInt256.ofNat (constructorRecordBase c)) = constructorScalarMemory c 19 := by
    unfold cometWithExtendedAssetListCreation_block_508_memory
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    rfl
  rw [hm19] at s19
  change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
    (initState σ σ₀ g A I)
    ⟨2789⟩ [UInt256.ofNat 1568, ⟨531⟩, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
    (constructorScalarMemory c 19) _ ByteArray.empty σ _ _ at s19
  obtain ⟨_, _, _, r19⟩ := cometCreationReadUint104 (by change 9 ≤ 1024; decide)
    (constructorScalarMemory_loadScalar c 19 19 (by decide) hsize)
    (show (constructorRecordWord c 19).toNat < 2^104 from
      constructorUintScalar_canonical ⟨104, by decide⟩ c.targetReserves)
    (by native_decide) s19
  exact ⟨_, _, _, r19⟩

end Benchmarks.CompoundIII.Comet

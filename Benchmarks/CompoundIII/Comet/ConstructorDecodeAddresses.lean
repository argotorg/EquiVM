import Benchmarks.CompoundIII.Comet.ConstructorRecordMemory
import Benchmarks.CompoundIII.Comet.CreationBlocks_002

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometConstructorDecodeAddresses {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig}
    {aw : UInt256} {k C : Nat}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨99⟩
      [⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c, UInt256.ofNat (constructorRecordBase c)]
      (constructorScalarMemory c 0) aw ByteArray.empty σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨193⟩
      [constructorRecordWord c 4, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
      (constructorScalarMemory c 4) aw' ByteArray.empty σ k' C' := by
  have s0 := cometWithExtendedAssetListCreation_block_99 (by change 7 ≤ 1024; decide)
    (by native_decide) h
  change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
    (initState σ σ₀ g A I)
    ⟨2747⟩ [UInt256.ofNat 960, ⟨112⟩, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
    (constructorScalarMemory c 0) _ ByteArray.empty σ _ _ at s0
  obtain ⟨_, _, _, r0⟩ := cometCreationReadAddress (by change 9 ≤ 1024; decide)
    (constructorScalarMemory_loadScalar c 0 0 (by decide) hsize)
    (show (constructorRecordWord c 0).toNat < 2^160 from
      constructorAddressScalar_canonical c.governor)
    (by native_decide) s0
  have s1 := cometWithExtendedAssetListCreation_block_112 (by change 8 ≤ 1024; decide)
    (by native_decide) r0
  have hm1 : cometWithExtendedAssetListCreation_block_112_memory
      (mem := constructorScalarMemory c 0) (x0 := constructorRecordWord c 0)
      (x4 := UInt256.ofNat (constructorRecordBase c)) = constructorScalarMemory c 1 := by
    unfold cometWithExtendedAssetListCreation_block_112_memory
    rw [constructorRecordBase_toNat hsize]
    rfl
  rw [hm1] at s1
  change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
    (initState σ σ₀ g A I)
    ⟨2747⟩ [UInt256.ofNat 992, ⟨130⟩, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
    (constructorScalarMemory c 1) _ ByteArray.empty σ _ _ at s1
  obtain ⟨_, _, _, r1⟩ := cometCreationReadAddress (by change 9 ≤ 1024; decide)
    (constructorScalarMemory_loadScalar c 1 1 (by decide) hsize)
    (show (constructorRecordWord c 1).toNat < 2^160 from
      constructorAddressScalar_canonical c.pauseGuardian)
    (by native_decide) s1
  have s2 := cometWithExtendedAssetListCreation_block_130 (by change 8 ≤ 1024; decide)
    (by native_decide) r1
  have hm2 : cometWithExtendedAssetListCreation_block_130_memory
      (mem := constructorScalarMemory c 1) (x0 := constructorRecordWord c 1)
      (x4 := UInt256.ofNat (constructorRecordBase c)) = constructorScalarMemory c 2 := by
    unfold cometWithExtendedAssetListCreation_block_130_memory
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    rfl
  rw [hm2] at s2
  change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
    (initState σ σ₀ g A I)
    ⟨2747⟩ [UInt256.ofNat 1024, ⟨151⟩, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
    (constructorScalarMemory c 2) _ ByteArray.empty σ _ _ at s2
  obtain ⟨_, _, _, r2⟩ := cometCreationReadAddress (by change 9 ≤ 1024; decide)
    (constructorScalarMemory_loadScalar c 2 2 (by decide) hsize)
    (show (constructorRecordWord c 2).toNat < 2^160 from
      constructorAddressScalar_canonical c.baseToken)
    (by native_decide) s2
  have s3 := cometWithExtendedAssetListCreation_block_151 (by change 8 ≤ 1024; decide)
    (by native_decide) r2
  have hm3 : cometWithExtendedAssetListCreation_block_151_memory
      (mem := constructorScalarMemory c 2) (x0 := constructorRecordWord c 2)
      (x4 := UInt256.ofNat (constructorRecordBase c)) = constructorScalarMemory c 3 := by
    unfold cometWithExtendedAssetListCreation_block_151_memory
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    rfl
  rw [hm3] at s3
  change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
    (initState σ σ₀ g A I)
    ⟨2747⟩ [UInt256.ofNat 1056, ⟨172⟩, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
    (constructorScalarMemory c 3) _ ByteArray.empty σ _ _ at s3
  obtain ⟨_, _, _, r3⟩ := cometCreationReadAddress (by change 9 ≤ 1024; decide)
    (constructorScalarMemory_loadScalar c 3 3 (by decide) hsize)
    (show (constructorRecordWord c 3).toNat < 2^160 from
      constructorAddressScalar_canonical c.baseTokenPriceFeed)
    (by native_decide) s3
  have s4 := cometWithExtendedAssetListCreation_block_172 (by change 8 ≤ 1024; decide)
    (by native_decide) r3
  have hm4 : cometWithExtendedAssetListCreation_block_172_memory
      (mem := constructorScalarMemory c 3) (x0 := constructorRecordWord c 3)
      (x4 := UInt256.ofNat (constructorRecordBase c)) = constructorScalarMemory c 4 := by
    unfold cometWithExtendedAssetListCreation_block_172_memory
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    rfl
  rw [hm4] at s4
  change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
    (initState σ σ₀ g A I)
    ⟨2747⟩ [UInt256.ofNat 1088, ⟨193⟩, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
    (constructorScalarMemory c 4) _ ByteArray.empty σ _ _ at s4
  obtain ⟨_, _, _, r4⟩ := cometCreationReadAddress (by change 9 ≤ 1024; decide)
    (constructorScalarMemory_loadScalar c 4 4 (by decide) hsize)
    (show (constructorRecordWord c 4).toNat < 2^160 from
      constructorAddressScalar_canonical c.extensionDelegate)
    (by native_decide) s4
  exact ⟨_, _, _, r4⟩

end Benchmarks.CompoundIII.Comet

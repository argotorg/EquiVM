import Benchmarks.CompoundIII.Comet.ConstructorDecodeAddresses
import Benchmarks.CompoundIII.Comet.CreationBlocks_002

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometConstructorDecodeUint64 {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig}
    {aw : UInt256} {k C : Nat}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨193⟩
      [constructorRecordWord c 4, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
      (constructorScalarMemory c 4) aw ByteArray.empty σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨462⟩
      [constructorRecordWord c 16, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
      (constructorScalarMemory c 16) aw' ByteArray.empty σ k' C' := by
  have s5 := cometWithExtendedAssetListCreation_block_193 (by change 8 ≤ 1024; decide)
    (by native_decide) h
  have hm5 : cometWithExtendedAssetListCreation_block_193_memory
      (mem := constructorScalarMemory c 4) (x0 := constructorRecordWord c 4)
      (x4 := UInt256.ofNat (constructorRecordBase c)) = constructorScalarMemory c 5 := by
    unfold cometWithExtendedAssetListCreation_block_193_memory
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    rfl
  rw [hm5] at s5
  change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
    (initState σ σ₀ g A I)
    ⟨2768⟩ [UInt256.ofNat 1120, ⟨214⟩, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
    (constructorScalarMemory c 5) _ ByteArray.empty σ _ _ at s5
  obtain ⟨_, _, _, r5⟩ := cometCreationReadUint64 (by change 9 ≤ 1024; decide)
    (constructorScalarMemory_loadScalar c 5 5 (by decide) hsize)
    (show (constructorRecordWord c 5).toNat < 2^64 from
      constructorUintScalar_canonical ⟨64, by decide⟩ c.supplyKink)
    (by native_decide) s5
  have s6 := cometWithExtendedAssetListCreation_block_214 (by change 8 ≤ 1024; decide)
    (by native_decide) r5
  have hm6 : cometWithExtendedAssetListCreation_block_214_memory
      (mem := constructorScalarMemory c 5) (x0 := constructorRecordWord c 5)
      (x4 := UInt256.ofNat (constructorRecordBase c)) = constructorScalarMemory c 6 := by
    unfold cometWithExtendedAssetListCreation_block_214_memory
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    rfl
  rw [hm6] at s6
  change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
    (initState σ σ₀ g A I)
    ⟨2768⟩ [UInt256.ofNat 1152, ⟨235⟩, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
    (constructorScalarMemory c 6) _ ByteArray.empty σ _ _ at s6
  obtain ⟨_, _, _, r6⟩ := cometCreationReadUint64 (by change 9 ≤ 1024; decide)
    (constructorScalarMemory_loadScalar c 6 6 (by decide) hsize)
    (show (constructorRecordWord c 6).toNat < 2^64 from
      constructorUintScalar_canonical ⟨64, by decide⟩ c.supplyPerYearInterestRateSlopeLow)
    (by native_decide) s6
  have s7 := cometWithExtendedAssetListCreation_block_235 (by change 8 ≤ 1024; decide)
    (by native_decide) r6
  have hm7 : cometWithExtendedAssetListCreation_block_235_memory
      (mem := constructorScalarMemory c 6) (x0 := constructorRecordWord c 6)
      (x4 := UInt256.ofNat (constructorRecordBase c)) = constructorScalarMemory c 7 := by
    unfold cometWithExtendedAssetListCreation_block_235_memory
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    rfl
  rw [hm7] at s7
  change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
    (initState σ σ₀ g A I)
    ⟨2768⟩ [UInt256.ofNat 1184, ⟨256⟩, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
    (constructorScalarMemory c 7) _ ByteArray.empty σ _ _ at s7
  obtain ⟨_, _, _, r7⟩ := cometCreationReadUint64 (by change 9 ≤ 1024; decide)
    (constructorScalarMemory_loadScalar c 7 7 (by decide) hsize)
    (show (constructorRecordWord c 7).toNat < 2^64 from
      constructorUintScalar_canonical ⟨64, by decide⟩ c.supplyPerYearInterestRateSlopeHigh)
    (by native_decide) s7
  have s8 := cometWithExtendedAssetListCreation_block_256 (by change 8 ≤ 1024; decide)
    (by native_decide) r7
  have hm8 : cometWithExtendedAssetListCreation_block_256_memory
      (mem := constructorScalarMemory c 7) (x0 := constructorRecordWord c 7)
      (x4 := UInt256.ofNat (constructorRecordBase c)) = constructorScalarMemory c 8 := by
    unfold cometWithExtendedAssetListCreation_block_256_memory
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    rfl
  rw [hm8] at s8
  change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
    (initState σ σ₀ g A I)
    ⟨2768⟩ [UInt256.ofNat 1216, ⟨278⟩, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
    (constructorScalarMemory c 8) _ ByteArray.empty σ _ _ at s8
  obtain ⟨_, _, _, r8⟩ := cometCreationReadUint64 (by change 9 ≤ 1024; decide)
    (constructorScalarMemory_loadScalar c 8 8 (by decide) hsize)
    (show (constructorRecordWord c 8).toNat < 2^64 from
      constructorUintScalar_canonical ⟨64, by decide⟩ c.supplyPerYearInterestRateBase)
    (by native_decide) s8
  have s9 := cometWithExtendedAssetListCreation_block_278 (by change 8 ≤ 1024; decide)
    (by native_decide) r8
  have hm9 : cometWithExtendedAssetListCreation_block_278_memory
      (mem := constructorScalarMemory c 8) (x0 := constructorRecordWord c 8)
      (x4 := UInt256.ofNat (constructorRecordBase c)) = constructorScalarMemory c 9 := by
    unfold cometWithExtendedAssetListCreation_block_278_memory
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    rfl
  rw [hm9] at s9
  change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
    (initState σ σ₀ g A I)
    ⟨2768⟩ [UInt256.ofNat 1248, ⟨301⟩, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
    (constructorScalarMemory c 9) _ ByteArray.empty σ _ _ at s9
  obtain ⟨_, _, _, r9⟩ := cometCreationReadUint64 (by change 9 ≤ 1024; decide)
    (constructorScalarMemory_loadScalar c 9 9 (by decide) hsize)
    (show (constructorRecordWord c 9).toNat < 2^64 from
      constructorUintScalar_canonical ⟨64, by decide⟩ c.borrowKink)
    (by native_decide) s9
  have s10 := cometWithExtendedAssetListCreation_block_301 (by change 8 ≤ 1024; decide)
    (by native_decide) r9
  have hm10 : cometWithExtendedAssetListCreation_block_301_memory
      (mem := constructorScalarMemory c 9) (x0 := constructorRecordWord c 9)
      (x4 := UInt256.ofNat (constructorRecordBase c)) = constructorScalarMemory c 10 := by
    unfold cometWithExtendedAssetListCreation_block_301_memory
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    rfl
  rw [hm10] at s10
  change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
    (initState σ σ₀ g A I)
    ⟨2768⟩ [UInt256.ofNat 1280, ⟨324⟩, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
    (constructorScalarMemory c 10) _ ByteArray.empty σ _ _ at s10
  obtain ⟨_, _, _, r10⟩ := cometCreationReadUint64 (by change 9 ≤ 1024; decide)
    (constructorScalarMemory_loadScalar c 10 10 (by decide) hsize)
    (show (constructorRecordWord c 10).toNat < 2^64 from
      constructorUintScalar_canonical ⟨64, by decide⟩ c.borrowPerYearInterestRateSlopeLow)
    (by native_decide) s10
  have s11 := cometWithExtendedAssetListCreation_block_324 (by change 8 ≤ 1024; decide)
    (by native_decide) r10
  have hm11 : cometWithExtendedAssetListCreation_block_324_memory
      (mem := constructorScalarMemory c 10) (x0 := constructorRecordWord c 10)
      (x4 := UInt256.ofNat (constructorRecordBase c)) = constructorScalarMemory c 11 := by
    unfold cometWithExtendedAssetListCreation_block_324_memory
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    rfl
  rw [hm11] at s11
  change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
    (initState σ σ₀ g A I)
    ⟨2768⟩ [UInt256.ofNat 1312, ⟨347⟩, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
    (constructorScalarMemory c 11) _ ByteArray.empty σ _ _ at s11
  obtain ⟨_, _, _, r11⟩ := cometCreationReadUint64 (by change 9 ≤ 1024; decide)
    (constructorScalarMemory_loadScalar c 11 11 (by decide) hsize)
    (show (constructorRecordWord c 11).toNat < 2^64 from
      constructorUintScalar_canonical ⟨64, by decide⟩ c.borrowPerYearInterestRateSlopeHigh)
    (by native_decide) s11
  have s12 := cometWithExtendedAssetListCreation_block_347 (by change 8 ≤ 1024; decide)
    (by native_decide) r11
  have hm12 : cometWithExtendedAssetListCreation_block_347_memory
      (mem := constructorScalarMemory c 11) (x0 := constructorRecordWord c 11)
      (x4 := UInt256.ofNat (constructorRecordBase c)) = constructorScalarMemory c 12 := by
    unfold cometWithExtendedAssetListCreation_block_347_memory
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    rfl
  rw [hm12] at s12
  change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
    (initState σ σ₀ g A I)
    ⟨2768⟩ [UInt256.ofNat 1344, ⟨370⟩, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
    (constructorScalarMemory c 12) _ ByteArray.empty σ _ _ at s12
  obtain ⟨_, _, _, r12⟩ := cometCreationReadUint64 (by change 9 ≤ 1024; decide)
    (constructorScalarMemory_loadScalar c 12 12 (by decide) hsize)
    (show (constructorRecordWord c 12).toNat < 2^64 from
      constructorUintScalar_canonical ⟨64, by decide⟩ c.borrowPerYearInterestRateBase)
    (by native_decide) s12
  have s13 := cometWithExtendedAssetListCreation_block_370 (by change 8 ≤ 1024; decide)
    (by native_decide) r12
  have hm13 : cometWithExtendedAssetListCreation_block_370_memory
      (mem := constructorScalarMemory c 12) (x0 := constructorRecordWord c 12)
      (x4 := UInt256.ofNat (constructorRecordBase c)) = constructorScalarMemory c 13 := by
    unfold cometWithExtendedAssetListCreation_block_370_memory
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    rfl
  rw [hm13] at s13
  change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
    (initState σ σ₀ g A I)
    ⟨2768⟩ [UInt256.ofNat 1376, ⟨393⟩, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
    (constructorScalarMemory c 13) _ ByteArray.empty σ _ _ at s13
  obtain ⟨_, _, _, r13⟩ := cometCreationReadUint64 (by change 9 ≤ 1024; decide)
    (constructorScalarMemory_loadScalar c 13 13 (by decide) hsize)
    (show (constructorRecordWord c 13).toNat < 2^64 from
      constructorUintScalar_canonical ⟨64, by decide⟩ c.storeFrontPriceFactor)
    (by native_decide) s13
  have s14 := cometWithExtendedAssetListCreation_block_393 (by change 8 ≤ 1024; decide)
    (by native_decide) r13
  have hm14 : cometWithExtendedAssetListCreation_block_393_memory
      (mem := constructorScalarMemory c 13) (x0 := constructorRecordWord c 13)
      (x4 := UInt256.ofNat (constructorRecordBase c)) = constructorScalarMemory c 14 := by
    unfold cometWithExtendedAssetListCreation_block_393_memory
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    rfl
  rw [hm14] at s14
  change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
    (initState σ σ₀ g A I)
    ⟨2768⟩ [UInt256.ofNat 1408, ⟨416⟩, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
    (constructorScalarMemory c 14) _ ByteArray.empty σ _ _ at s14
  obtain ⟨_, _, _, r14⟩ := cometCreationReadUint64 (by change 9 ≤ 1024; decide)
    (constructorScalarMemory_loadScalar c 14 14 (by decide) hsize)
    (show (constructorRecordWord c 14).toNat < 2^64 from
      constructorUintScalar_canonical ⟨64, by decide⟩ c.trackingIndexScale)
    (by native_decide) s14
  have s15 := cometWithExtendedAssetListCreation_block_416 (by change 8 ≤ 1024; decide)
    (by native_decide) r14
  have hm15 : cometWithExtendedAssetListCreation_block_416_memory
      (mem := constructorScalarMemory c 14) (x0 := constructorRecordWord c 14)
      (x4 := UInt256.ofNat (constructorRecordBase c)) = constructorScalarMemory c 15 := by
    unfold cometWithExtendedAssetListCreation_block_416_memory
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    rfl
  rw [hm15] at s15
  change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
    (initState σ σ₀ g A I)
    ⟨2768⟩ [UInt256.ofNat 1440, ⟨439⟩, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
    (constructorScalarMemory c 15) _ ByteArray.empty σ _ _ at s15
  obtain ⟨_, _, _, r15⟩ := cometCreationReadUint64 (by change 9 ≤ 1024; decide)
    (constructorScalarMemory_loadScalar c 15 15 (by decide) hsize)
    (show (constructorRecordWord c 15).toNat < 2^64 from
      constructorUintScalar_canonical ⟨64, by decide⟩ c.baseTrackingSupplySpeed)
    (by native_decide) s15
  have s16 := cometWithExtendedAssetListCreation_block_439 (by change 8 ≤ 1024; decide)
    (by native_decide) r15
  have hm16 : cometWithExtendedAssetListCreation_block_439_memory
      (mem := constructorScalarMemory c 15) (x0 := constructorRecordWord c 15)
      (x4 := UInt256.ofNat (constructorRecordBase c)) = constructorScalarMemory c 16 := by
    unfold cometWithExtendedAssetListCreation_block_439_memory
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    rfl
  rw [hm16] at s16
  change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
    (initState σ σ₀ g A I)
    ⟨2768⟩ [UInt256.ofNat 1472, ⟨462⟩, ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
      UInt256.ofNat (constructorRecordBase c)]
    (constructorScalarMemory c 16) _ ByteArray.empty σ _ _ at s16
  obtain ⟨_, _, _, r16⟩ := cometCreationReadUint64 (by change 9 ≤ 1024; decide)
    (constructorScalarMemory_loadScalar c 16 16 (by decide) hsize)
    (show (constructorRecordWord c 16).toNat < 2^64 from
      constructorUintScalar_canonical ⟨64, by decide⟩ c.baseTrackingBorrowSpeed)
    (by native_decide) s16
  exact ⟨_, _, _, r16⟩

end Benchmarks.CompoundIII.Comet

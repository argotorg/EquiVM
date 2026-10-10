import Benchmarks.CompoundIII.Comet.ConstructorDecodeScalars

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem constructorAssetArraySize {n : Nat} (hn : n < 2^64) :
    UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) + UInt256.ofNat 32 =
      UInt256.ofNat (32 + 32 * n) := by
  change UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩ + UInt256.ofNat 32 = _
  rw [shiftLeft5_ofNat_eq (by change _ < 2^256; omega)]
  apply u256_inj
  change (UInt256.add (UInt256.ofNat (32 * n)) (UInt256.ofNat 32)).toNat = _
  rw [uadd_ofNat_toNat (by change _ < 2^256; omega) (by decide)
    (by change _ < 2^256; omega), UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)]
  omega

/-- Validate the asset-array head and reach its pointer-array allocation. -/
theorem cometConstructorAssetHeader {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig}
    {aw : UInt256} {k C : Nat}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (hrecord : constructorRecordBase c + 672 < 2^64)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨562⟩
      [constructorArgumentSizeWord c, ⟨928⟩, ⟨32⟩, ⟨672⟩,
        UInt256.ofNat (constructorRecordBase c)]
      (constructorScalarMemory c 20) aw ByteArray.empty σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨2711⟩
      [UInt256.ofNat (constructorRecordBase c + 672),
        UInt256.ofNat (32 + 32 * c.assetConfigs.length), ⟨623⟩, ⟨672⟩, ⟨928⟩,
        constructorArgumentSizeWord c, UInt256.ofNat c.assetConfigs.length, ⟨32⟩,
        UInt256.ofNat (constructorRecordBase c + 672), UInt256.ofNat (constructorRecordBase c)]
      (constructorScalarMemory c 20) aw' ByteArray.empty σ k' C' := by
  have hn : c.assetConfigs.length < 2^64 := by unfold constructorRecordBase at hrecord; omega
  have hend : (⟨928⟩ : UInt256) + constructorArgumentSizeWord c =
      UInt256.ofNat (constructorRecordBase c) := by
    apply u256_inj
    rw [uadd_toNat, constructorArgumentSizeWord, constructorArgumentSize_toNat hsize,
      constructorRecordBase_toNat hsize]
    change (928 + (736 + 224 * c.assetConfigs.length)) % UInt256.size = _
    rw [Nat.mod_eq_of_lt (by omega)]
    unfold constructorRecordBase
    omega
  have hleft : (((⟨928⟩ : UInt256) + ⟨32⟩) + ⟨672⟩) + UInt256.ofNat 31 =
      UInt256.ofNat 1663 := by decide
  have r1 := cometWithExtendedAssetListCreation_block_562_fallthrough
    (by change 10 ≤ 1024; decide) (by
      rw [hend, hleft, slt_ofNat_lit_one_low (by omega)
        (by unfold constructorRecordBase; omega)]
      rfl) h
  have hlength : memLoad ((⟨672⟩ : UInt256) + (⟨32⟩ + ⟨928⟩))
      (constructorScalarMemory c 20) = UInt256.ofNat c.assetConfigs.length :=
    constructorScalarMemory_arrayLength c 20 hsize
  have r2 := cometWithExtendedAssetListCreation_block_580_fallthrough
    (by change 9 ≤ 1024; decide) (by
      rw [hlength]
      apply ugt_zero
      rw [constructorAssetCount_toNat hsize]
      change _ ≤ 2^64 - 1
      omega) r1
  simp only [cometWithExtendedAssetListCreation_block_580_fallthrough_stack, hlength] at r2
  have r3 := cometWithExtendedAssetListCreation_block_602
    (by change 11 ≤ 1024; decide) (by native_decide) r2
  simp only [cometWithExtendedAssetListCreation_block_602_stack,
    constructorScalarMemory_free, constructorAssetArraySize hn] at r3
  exact ⟨_, _, _, r3⟩

end Benchmarks.CompoundIII.Comet

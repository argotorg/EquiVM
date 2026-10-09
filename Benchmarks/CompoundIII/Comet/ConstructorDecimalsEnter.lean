import Benchmarks.CompoundIII.Comet.ConstructorDecodedMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def constructorDecimalsMemory (c : ConstructorConfig) : ByteArray :=
  writeWord (constructorDecodedMemory c) (constructorAssetFree c c.assetConfigs.length)
    (UInt256.shiftLeft (UInt256.ofNat 826074471) (UInt256.ofNat 224))

private theorem constructorDecimalsGasCost (C a b c d : Nat) :
    C + (102 + a + b + c + d) + 2 = C + (104 + a + b + c + d) := by omega

/-- Store the asset-array pointer, read the base token, and prepare its decimals call. -/
theorem cometConstructorDecimalsEnter {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig}
    {aw : UInt256} {k C : Nat}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨685⟩ (constructorAssetLoopStack c c.assetConfigs.length)
      (constructorAssetLoopMemory c c.assetConfigs.length) aw ByteArray.empty σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨733⟩
      ((g.subNat C').toUInt256 :: constructorRecordWord c 2 ::
        UInt256.ofNat (constructorAssetFree c c.assetConfigs.length) :: ⟨4⟩ ::
        UInt256.ofNat (constructorAssetFree c c.assetConfigs.length) :: ⟨32⟩ ::
        UInt256.ofNat (constructorAssetFree c c.assetConfigs.length) ::
        UInt256.ofNat (constructorRecordBase c) ::
        constructorAssetLoopStack c c.assetConfigs.length)
      (constructorDecimalsMemory c) aw' ByteArray.empty σ k' C' := by
  have hm : (UInt256.ofNat (constructorArrayBase c)).toByteArray.write 0
      (constructorAssetLoopMemory c c.assetConfigs.length)
      (UInt256.ofNat (constructorRecordBase c) + UInt256.ofNat 640).toNat 32 =
        constructorDecodedMemory c := by
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    rfl
  have hb : memLoad (UInt256.ofNat (constructorRecordBase c) + UInt256.ofNat 64)
      (constructorDecodedMemory c) = constructorRecordWord c 2 :=
    constructorDecodedMemory_scalar (c := c) (j := 2) (by decide) hsize
  have hclean : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (constructorRecordWord c 2) = constructorRecordWord c 2 := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 160) _ _ (by native_decide)
      (constructorAddressScalar_canonical c.baseToken)
  have hptr : (UInt256.ofNat (constructorAssetFree c c.assetConfigs.length)).toNat =
      constructorAssetFree c c.assetConfigs.length :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have r := cometWithExtendedAssetListCreation_block_685 (by change 19 ≤ 1024; decide) h
  simp only [cometWithExtendedAssetListCreation_block_685_stack,
    cometWithExtendedAssetListCreation_block_685_memory, hm, hb, constructorDecodedMemory_free,
    hclean, hptr, constructorDecimalsGasCost] at r
  exact ⟨_, _, _, r⟩

/-- Decode the constructor arguments and reach its first external call, or fail allocation. -/
theorem cometConstructorDecodeToDecimals {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig}
    (hcode : I.code = cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
    (hv : I.weiValue = ⟨0⟩) (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    if constructorAssetFree c c.assetConfigs.length < 2^64 then
      ∃ aw k C, RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
        (initState σ σ₀ g A I) ⟨733⟩
        ((g.subNat C).toUInt256 :: constructorRecordWord c 2 ::
          UInt256.ofNat (constructorAssetFree c c.assetConfigs.length) :: ⟨4⟩ ::
          UInt256.ofNat (constructorAssetFree c c.assetConfigs.length) :: ⟨32⟩ ::
          UInt256.ofNat (constructorAssetFree c c.assetConfigs.length) ::
          UInt256.ofNat (constructorRecordBase c) ::
          constructorAssetLoopStack c c.assetConfigs.length)
        (constructorDecimalsMemory c) aw ByteArray.empty σ k C
    else RDrev (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) g
      (initState σ σ₀ g A I) := by
  have decoded := cometConstructorDecode (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hv hsize
  split
  · rename_i hfree
    rw [if_pos hfree] at decoded
    obtain ⟨_, _, _, hdecoded⟩ := decoded
    exact cometConstructorDecimalsEnter hsize hfree hdecoded
  · rename_i hfree
    rw [if_neg hfree] at decoded
    exact decoded

end Benchmarks.CompoundIII.Comet

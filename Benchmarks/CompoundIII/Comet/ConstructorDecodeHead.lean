import Benchmarks.CompoundIII.Comet.ConstructorMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

/-- Copy and validate the outer tuple head, stopping before allocation of the decoded record. -/
theorem cometConstructorDecodeHead {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig}
    {aw : UInt256} {k C : Nat}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (hsmall : 1664 + 224 * c.assetConfigs.length < 2^64)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨33⟩
      [⟨21425⟩, constructorArgumentSizeWord c, constructorArgumentSizeWord c, ⟨928⟩]
      (constructorAllocatedMemory c) aw ByteArray.empty σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨2711⟩
      [UInt256.ofNat (1664 + 224 * c.assetConfigs.length), ⟨672⟩, ⟨99⟩,
        ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
        UInt256.ofNat (1664 + 224 * c.assetConfigs.length)]
      (constructorCopiedMemory c) aw' ByteArray.empty σ k' C' := by
  have hlen := constructorArgumentSize_toNat hsize
  have hsub : UInt256.sub ((⟨928⟩ : UInt256) + constructorArgumentSizeWord c) ⟨928⟩ =
      constructorArgumentSizeWord c :=
    usub_uadd_lit_cancel (base := 928) (n := 736 + 224 * c.assetConfigs.length)
      (by decide) (by omega) (by omega)
  have r1 := cometWithExtendedAssetListCreation_block_33_fallthrough (by decide) (by
    rw [hsub]
    exact slt_lit_zero (by decide) (by exact Nat.le_trans (by omega) (Nat.le_of_eq hlen.symm))
      (by change (UInt256.ofNat (736 + 224 * c.assetConfigs.length)).toNat < _; rw [hlen]; omega)) h
  have hmem : cometWithExtendedAssetListCreation_block_33_fallthrough_memory
      (tail := c.encodedArgs.toByteArray) (mem := constructorAllocatedMemory c)
      (x0 := ⟨21425⟩) (x1 := constructorArgumentSizeWord c) (x3 := ⟨928⟩) =
      constructorCopiedMemory c := by
    unfold cometWithExtendedAssetListCreation_block_33_fallthrough_memory
    change (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray).write 21425
      (constructorAllocatedMemory c) 928 (constructorArgumentSizeWord c).toNat = _
    rw [constructorArgumentSizeWord, hlen, ← ConstructorConfig.encodedArgs_length]
    exact constructorCodecopy c
  rw [hmem] at r1
  have r2 := cometWithExtendedAssetListCreation_block_49_fallthrough (by decide) (by
    rw [constructorCopiedMemory_outerOffset c hsize]
    native_decide) r1
  simp only [cometWithExtendedAssetListCreation_block_49_fallthrough_stack,
    constructorCopiedMemory_outerOffset c hsize] at r2
  have hadd : ((⟨928⟩ : UInt256) + constructorArgumentSizeWord c).toNat =
      1664 + 224 * c.assetConfigs.length := by
    rw [uadd_toNat]
    change (928 + (constructorArgumentSizeWord c).toNat) % UInt256.size = _
    rw [constructorArgumentSizeWord, hlen, Nat.mod_eq_of_lt (by omega)]
    omega
  have htail : (UInt256.sub ((⟨928⟩ : UInt256) + constructorArgumentSizeWord c)
      ((⟨928⟩ : UInt256) + ⟨32⟩)).toNat = 704 + 224 * c.assetConfigs.length := by
    have h960 : ((⟨928⟩ : UInt256) + ⟨32⟩).toNat = 960 := by decide
    rw [usub_toNat (by rw [hadd, h960]; omega), hadd, h960]
    omega
  have r3 := cometWithExtendedAssetListCreation_block_66_fallthrough (by decide) (by
    apply slt_lit_zero (by decide)
    · rw [htail]; omega
    · rw [htail]; omega) r2
  have r4 := cometWithExtendedAssetListCreation_block_82 (by decide) (by native_decide) r3
  simp only [cometWithExtendedAssetListCreation_block_82_stack, constructorCopiedMemory_free] at r4
  exact ⟨_, _, _, r4⟩

/-- Complete constructor entry and outer-tuple decoding, including allocation failure. -/
theorem cometConstructorDecodeStart {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig}
    (hcode : I.code = cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
    (hv : I.weiValue = ⟨0⟩) (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    if 1664 + 224 * c.assetConfigs.length < 2^64 then
      ∃ aw k C, RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
        (initState σ σ₀ g A I) ⟨2711⟩
        [UInt256.ofNat (1664 + 224 * c.assetConfigs.length), ⟨672⟩, ⟨99⟩,
          ⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c,
          UInt256.ofNat (1664 + 224 * c.assetConfigs.length)]
        (constructorCopiedMemory c) aw ByteArray.empty σ k C
    else RDrev (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) g
      (initState σ σ₀ g A I) := by
  obtain ⟨aw, k, C, rentry⟩ := cometConstructorEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) hcode hv hsize
  split
  · rename_i hsmall
    obtain ⟨_, _, _, rcopy⟩ := cometConstructorAllocate hsize hsmall rentry
    exact cometConstructorDecodeHead hsize hsmall rcopy
  · rename_i hlarge
    exact cometConstructorAllocationOverflow hsize (Nat.le_of_not_lt hlarge) rentry

end Benchmarks.CompoundIII.Comet

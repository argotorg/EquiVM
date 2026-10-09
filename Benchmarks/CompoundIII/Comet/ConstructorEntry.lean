import Benchmarks.CompoundIII.Comet.ConstructorAllocationWords
import Benchmarks.CompoundIII.Comet.CreationBlocks_001
import Benchmarks.CompoundIII.Comet.CreationBlocks_008

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

def constructorArgumentSizeWord (c : ConstructorConfig) : UInt256 :=
  UInt256.ofNat (736 + 224 * c.assetConfigs.length)

def constructorEntryMemory : ByteArray := writeWord ByteArray.empty 64 ⟨928⟩

/-- Reach the initial argument allocation using the exact, nonwrapping argument size. -/
theorem cometConstructorEntry {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig}
    (hcode : I.code = cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
    (hv : I.weiValue = ⟨0⟩) (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    ∃ aw k C, RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨2711⟩
      [⟨928⟩, constructorArgumentSizeWord c, ⟨33⟩, ⟨21425⟩,
        constructorArgumentSizeWord c, constructorArgumentSizeWord c, ⟨928⟩]
      constructorEntryMemory aw ByteArray.empty σ k C := by
  have hfull : (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray).size <
      UInt256.size := by
    simpa only [ByteArray.size_append, cometCreationBytecode_size, List.size_toByteArray,
      ConstructorConfig.encodedArgs_length, ← Nat.add_assoc] using hsize
  have hlength : UInt256.sub
      (UInt256.ofNat (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray).size)
      (UInt256.ofNat 21425) = constructorArgumentSizeWord c := by
    apply u256_inj
    rw [cometConstructorCodeSize hfull, List.size_toByteArray,
      ConstructorConfig.encodedArgs_length, constructorArgumentSizeWord,
      constructorArgumentSize_toNat hsize]
  have r0 := RD.initState (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode
  have r1 := cometWithExtendedAssetListCreation_block_0_fallthrough (by decide) hv r0
  have r2 := cometWithExtendedAssetListCreation_block_13 (by decide) (by native_decide) r1
  simp only [cometWithExtendedAssetListCreation_block_13_stack,
    cometWithExtendedAssetListCreation_block_0_fallthrough_memory, hlength] at r2
  exact ⟨_, _, _, r2⟩

def constructorAllocatedMemory (c : ConstructorConfig) : ByteArray :=
  writeWord constructorEntryMemory 64 (UInt256.ofNat (1664 + 224 * c.assetConfigs.length))

theorem cometConstructorAllocate {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig}
    {aw : UInt256} {k C : Nat}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (hsmall : 1664 + 224 * c.assetConfigs.length < 2^64)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨2711⟩
      [⟨928⟩, constructorArgumentSizeWord c, ⟨33⟩, ⟨21425⟩,
        constructorArgumentSizeWord c, constructorArgumentSizeWord c, ⟨928⟩]
      constructorEntryMemory aw ByteArray.empty σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨33⟩
      [⟨21425⟩, constructorArgumentSizeWord c, constructorArgumentSizeWord c, ⟨928⟩]
      (constructorAllocatedMemory c) aw' ByteArray.empty σ k' C' := by
  have r1 := cometWithExtendedAssetListCreation_block_2711_fallthrough (by change 10 ≤ 1024; decide)
    (constructorAllocationGuard_zero hsize hsmall) h
  have r2 := cometWithExtendedAssetListCreation_block_2743 (by change 7 ≤ 1024; decide)
    (by native_decide) r1
  change ∃ aw' k' C', RD _ _ _ _ _ _
    (writeWord constructorEntryMemory 64 (UInt256.ofNat (1664 + 224 * c.assetConfigs.length)))
    aw' ByteArray.empty σ k' C'
  have hend := constructorAllocationEnd_eq hsize
  change ((⟨928⟩ : UInt256) + UInt256.land (UInt256.lnot (UInt256.ofNat 31))
    (UInt256.ofNat (736 + 224 * c.assetConfigs.length) + UInt256.ofNat 31)) = _ at hend
  simp only [cometWithExtendedAssetListCreation_block_2743_memory, hend] at r2
  exact ⟨_, _, _, r2⟩

theorem cometConstructorAllocationOverflow {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig}
    {aw : UInt256} {k C : Nat}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (hlarge : 2^64 ≤ 1664 + 224 * c.assetConfigs.length)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨2711⟩
      [⟨928⟩, constructorArgumentSizeWord c, ⟨33⟩, ⟨21425⟩,
        constructorArgumentSizeWord c, constructorArgumentSizeWord c, ⟨928⟩]
      constructorEntryMemory aw ByteArray.empty σ k C) :
    RDrev (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) g
      (initState σ σ₀ g A I) := by
  have r1 := cometWithExtendedAssetListCreation_block_2711_taken (by change 10 ≤ 1024; decide)
    (constructorAllocationGuard_ne_zero hsize hlarge) (by native_decide) h
  exact cometWithExtendedAssetListCreation_block_2689 (by change 8 ≤ 1024; decide) r1

end Benchmarks.CompoundIII.Comet

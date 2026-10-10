import Benchmarks.CompoundIII.Comet.ConstructorDecodeUint104

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

/-- Decode all twenty fixed fields and validate the asset-array offset. -/
theorem cometConstructorDecodeScalars {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig}
    {aw : UInt256} {k C : Nat}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨99⟩
      [⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c, UInt256.ofNat (constructorRecordBase c)]
      (constructorRecordMemory c) aw ByteArray.empty σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨562⟩
      [constructorArgumentSizeWord c, ⟨928⟩, ⟨32⟩, ⟨672⟩, UInt256.ofNat (constructorRecordBase c)]
      (constructorScalarMemory c 20) aw' ByteArray.empty σ k' C' := by
  obtain ⟨_, _, _, r1⟩ := cometConstructorDecodeAddresses hsize h
  obtain ⟨_, _, _, r2⟩ := cometConstructorDecodeUint64 hsize r1
  obtain ⟨_, _, _, r3⟩ := cometConstructorDecodeUint104 hsize r2
  have hm : (constructorRecordWord c 19).toByteArray.write 0 (constructorScalarMemory c 19)
      (UInt256.ofNat (constructorRecordBase c) + UInt256.ofNat 608).toNat 32 =
      constructorScalarMemory c 20 := by
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    rfl
  have hread : memLoad (UInt256.ofNat 640 + ((⟨32⟩ : UInt256) + ⟨928⟩))
      (constructorScalarMemory c 20) = ⟨672⟩ :=
    constructorScalarMemory_arrayOffset c 20 hsize
  have r4 := cometWithExtendedAssetListCreation_block_531_fallthrough
    (by change 8 ≤ 1024; decide) (by rw [hm, hread]; native_decide) r3
  simp only [cometWithExtendedAssetListCreation_block_531_fallthrough_stack,
    cometWithExtendedAssetListCreation_block_531_fallthrough_memory, hm, hread] at r4
  exact ⟨_, _, _, r4⟩

/-- The complete fixed-field decoder, including both allocation-failure branches. -/
theorem cometConstructorDecodeRecord {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig}
    (hcode : I.code = cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
    (hv : I.weiValue = ⟨0⟩) (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    if constructorRecordBase c + 672 < 2^64 then
      ∃ aw k C, RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
        (initState σ σ₀ g A I) ⟨562⟩
        [constructorArgumentSizeWord c, ⟨928⟩, ⟨32⟩, ⟨672⟩,
          UInt256.ofNat (constructorRecordBase c)]
        (constructorScalarMemory c 20) aw ByteArray.empty σ k C
    else RDrev (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) g
      (initState σ σ₀ g A I) := by
  have hr := cometConstructorDecodeStart (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hv hsize
  by_cases hfirst : 1664 + 224 * c.assetConfigs.length < 2^64
  · rw [if_pos hfirst] at hr
    obtain ⟨_, _, _, rhead⟩ := hr
    have hr := cometConstructorRecordAllocate hsize rhead
    split
    · rename_i hrecord
      rw [if_pos hrecord] at hr
      obtain ⟨_, _, _, rrecord⟩ := hr
      exact cometConstructorDecodeScalars hsize rrecord
    · rename_i hrecord
      rw [if_neg hrecord] at hr
      exact hr
  · rw [if_neg hfirst] at hr
    have hrecord : ¬ constructorRecordBase c + 672 < 2^64 := by
      unfold constructorRecordBase
      omega
    rw [if_neg hrecord]
    exact hr

end Benchmarks.CompoundIII.Comet

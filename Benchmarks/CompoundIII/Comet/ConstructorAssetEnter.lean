import Benchmarks.CompoundIII.Comet.ConstructorAssetAllocation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def constructorAssetsDataEnd (c : ConstructorConfig) : UInt256 :=
  ((((⟨928⟩ : UInt256) + ⟨32⟩) + ⟨672⟩) +
    UInt256.mul (UInt256.ofNat c.assetConfigs.length) (UInt256.ofNat 224)) + UInt256.ofNat 32

theorem constructorAssetsDataEnd_toNat {c : ConstructorConfig}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    (constructorAssetsDataEnd c).toNat = constructorRecordBase c := by
  have hm : (UInt256.mul (UInt256.ofNat c.assetConfigs.length) (UInt256.ofNat 224)).toNat =
      224 * c.assetConfigs.length := by
    rw [u256_mul_toNat, constructorAssetCount_toNat hsize]
    change (c.assetConfigs.length * 224) % UInt256.size = _
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hp : ((((⟨928⟩ : UInt256) + ⟨32⟩) + ⟨672⟩) +
      UInt256.mul (UInt256.ofNat c.assetConfigs.length) (UInt256.ofNat 224)).toNat =
      1632 + 224 * c.assetConfigs.length := by
    rw [uadd_toNat, hm]
    change (1632 + 224 * c.assetConfigs.length) % UInt256.size = _
    exact Nat.mod_eq_of_lt (by omega)
  rw [constructorAssetsDataEnd, uadd_toNat, hp]
  change (1632 + 224 * c.assetConfigs.length + 32) % UInt256.size = _
  rw [Nat.mod_eq_of_lt (by omega)]
  unfold constructorRecordBase
  omega

theorem constructorArgumentEnd_toNat {c : ConstructorConfig}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    ((⟨928⟩ : UInt256) + constructorArgumentSizeWord c).toNat = constructorRecordBase c := by
  rw [uadd_toNat, constructorArgumentSizeWord, constructorArgumentSize_toNat hsize]
  change (928 + (736 + 224 * c.assetConfigs.length)) % UInt256.size = _
  rw [Nat.mod_eq_of_lt (by omega)]
  unfold constructorRecordBase
  omega

def constructorArrayHeaderMemory (c : ConstructorConfig) : ByteArray :=
  writeWord (constructorArrayMemory c) (constructorArrayBase c)
    (UInt256.ofNat c.assetConfigs.length)

/-- Store the array length and reach the element loop after its payload-bound check. -/
theorem cometConstructorAssetEnter {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig}
    {aw : UInt256} {k C : Nat}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (harray : constructorArrayEnd c < 2^64)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨623⟩
      [⟨672⟩, ⟨928⟩, constructorArgumentSizeWord c, UInt256.ofNat c.assetConfigs.length,
        ⟨32⟩, UInt256.ofNat (constructorArrayBase c), UInt256.ofNat (constructorRecordBase c)]
      (constructorArrayMemory c) aw ByteArray.empty σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨664⟩
      [⟨672⟩, ⟨32⟩, UInt256.ofNat (constructorArrayBase c + 32), ⟨928⟩,
        constructorArgumentSizeWord c, UInt256.ofNat c.assetConfigs.length, ⟨1664⟩,
        UInt256.ofNat (constructorArrayBase c), UInt256.ofNat (constructorRecordBase c)]
      (constructorArrayHeaderMemory c) aw' ByteArray.empty σ k' C' := by
  have hbase : (UInt256.ofNat (constructorArrayBase c)).toNat = constructorArrayBase c :=
    UInt256.toNat_ofNat_of_lt (by
      unfold constructorArrayEnd at harray; change _ < 2^256; omega)
  have hnext : UInt256.ofNat (constructorArrayBase c) + UInt256.ofNat 32 =
      UInt256.ofNat (constructorArrayBase c + 32) := by
    apply u256_inj
    rw [uadd_toNat, hbase]
    rfl
  have r1 := cometWithExtendedAssetListCreation_block_623_fallthrough
    (by change 14 ≤ 1024; decide) (by
      apply ugt_zero
      change (constructorAssetsDataEnd c).toNat ≤ _
      rw [constructorAssetsDataEnd_toNat hsize, constructorArgumentEnd_toNat hsize]) h
  have r2 := cometWithExtendedAssetListCreation_block_654 (by change 10 ≤ 1024; decide) r1
  simp only [cometWithExtendedAssetListCreation_block_654_stack,
    cometWithExtendedAssetListCreation_block_623_fallthrough_memory, hbase, hnext] at r2
  exact ⟨_, _, _, r2⟩

/-- Constructor decoding through the asset-loop entry, including all preceding
    allocation failures. -/
theorem cometConstructorDecodeToAssets {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig}
    (hcode : I.code = cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
    (hv : I.weiValue = ⟨0⟩) (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    if constructorArrayEnd c < 2^64 then
      ∃ aw k C, RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
        (initState σ σ₀ g A I) ⟨664⟩
        [⟨672⟩, ⟨32⟩, UInt256.ofNat (constructorArrayBase c + 32), ⟨928⟩,
          constructorArgumentSizeWord c, UInt256.ofNat c.assetConfigs.length, ⟨1664⟩,
          UInt256.ofNat (constructorArrayBase c), UInt256.ofNat (constructorRecordBase c)]
        (constructorArrayHeaderMemory c) aw ByteArray.empty σ k C
    else RDrev (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) g
      (initState σ σ₀ g A I) := by
  have hr := cometConstructorDecodeRecord (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hv hsize
  by_cases hrecord : constructorRecordBase c + 672 < 2^64
  · rw [if_pos hrecord] at hr
    obtain ⟨_, _, _, rrecord⟩ := hr
    obtain ⟨_, _, _, rheader⟩ := cometConstructorAssetHeader hsize hrecord rrecord
    have hr := cometConstructorArrayAllocate hrecord rheader
    split
    · rename_i harray
      rw [if_pos harray] at hr
      obtain ⟨_, _, _, rarray⟩ := hr
      exact cometConstructorAssetEnter hsize harray rarray
    · rename_i harray
      rw [if_neg harray] at hr
      exact hr
  · rw [if_neg hrecord] at hr
    have harray : ¬ constructorArrayEnd c < 2^64 := by
      unfold constructorArrayEnd constructorArrayBase
      omega
    rw [if_neg harray]
    exact hr

end Benchmarks.CompoundIII.Comet

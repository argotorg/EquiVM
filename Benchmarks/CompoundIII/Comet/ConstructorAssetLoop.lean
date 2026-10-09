import Benchmarks.CompoundIII.Comet.ConstructorAssetLoopMemory
import Benchmarks.CompoundIII.Comet.CreationBlocks_003

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def constructorAssetLoopStack (c : ConstructorConfig) (i : Nat) : List UInt256 :=
  [⟨672⟩, ⟨32⟩, UInt256.ofNat (constructorAssetEntry c i), ⟨928⟩,
    constructorArgumentSizeWord c, UInt256.ofNat c.assetConfigs.length,
    UInt256.ofNat (1664 + 224 * i), UInt256.ofNat (constructorArrayBase c),
    UInt256.ofNat (constructorRecordBase c)]

theorem constructorAssetAllocationEnd {ptr : Nat} (hp : ptr < 2^64) :
    allocationEnd (UInt256.ofNat ptr) (UInt256.ofNat 224) = UInt256.ofNat (ptr + 224) := by
  change UInt256.ofNat ptr + UInt256.ofNat 224 = _
  apply u256_inj
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)]
  rfl

theorem constructorAssetAllocationGuard {ptr : Nat} (hp : ptr < 2^64) :
    constructorAllocationGuard (UInt256.ofNat ptr) (UInt256.ofNat 224) = ⟨0⟩ ↔
      ptr + 224 < 2^64 := by
  apply constructorAllocationGuard_iff (endPos := ptr + 224)
  · rw [constructorAssetAllocationEnd hp, UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)]
  · rw [UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)]
    omega

/-- A single asset iteration, including the allocator's failure branch. -/
theorem cometConstructorAssetStep {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig} {i : Nat}
    {aw : UInt256} {k C : Nat}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (hi : i < c.assetConfigs.length) (hfree : constructorAssetFree c i < 2^64)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨664⟩ (constructorAssetLoopStack c i)
      (constructorAssetLoopMemory c i) aw ByteArray.empty σ k C) :
    if constructorAssetFree c (i + 1) < 2^64 then
      ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
        (initState σ σ₀ g A I) ⟨664⟩ (constructorAssetLoopStack c (i + 1))
        (constructorAssetLoopMemory c (i + 1)) aw' ByteArray.empty σ k' C'
    else RDrev (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) g
      (initState σ σ₀ g A I) := by
  have hrecord : constructorRecordBase c < 2^64 := by
    unfold constructorAssetFree constructorArrayEnd constructorArrayBase at hfree
    omega
  have hsrc : (UInt256.ofNat (1664 + 224 * i)).toNat = 1664 + 224 * i :=
    UInt256.toNat_ofNat_of_lt (by omega)
  have r1 := cometWithExtendedAssetListCreation_block_664_taken
    (by change 14 ≤ 1024; decide) (by
      change UInt256.lt (UInt256.ofNat (1664 + 224 * i)) (constructorAssetsDataEnd c) ≠ ⟨0⟩
      rw [ult_one (by
        rw [hsrc, constructorAssetsDataEnd_toNat hsize]
        unfold constructorRecordBase
        omega)]
      decide) (by native_decide) h
  have hremaining : UInt256.sub ((⟨928⟩ : UInt256) + constructorArgumentSizeWord c)
      (UInt256.ofNat (1664 + 224 * i)) =
      UInt256.ofNat (224 * (c.assetConfigs.length - i)) := by
    apply u256_inj
    rw [usub_toNat (by
        rw [constructorArgumentEnd_toNat hsize, hsrc]
        unfold constructorRecordBase; omega),
      constructorArgumentEnd_toNat hsize, hsrc,
      UInt256.toNat_ofNat_of_lt (by omega)]
    unfold constructorRecordBase
    omega
  have r2 := cometWithExtendedAssetListCreation_block_2494_fallthrough
    (by change 13 ≤ 1024; decide) (by
      rw [hremaining]
      exact slt_ofNat_lit_zero (by decide) (by unfold constructorRecordBase at hrecord; omega)
        (by unfold constructorRecordBase at hrecord; omega)) r1
  have r3 := cometWithExtendedAssetListCreation_block_2508
    (by change 14 ≤ 1024; decide) (by native_decide) r2
  have hloadFree : memLoad (UInt256.ofNat 64) (constructorAssetLoopMemory c i) =
      UInt256.ofNat (constructorAssetFree c i) := constructorAssetLoopMemory_free (Nat.le_of_lt hi)
  simp only [cometWithExtendedAssetListCreation_block_2508_stack, hloadFree] at r3
  have r4 := cometCreationAllocate (by change 16 ≤ 1024; decide) (by native_decide) r3
  have hnext : constructorAssetFree c i + 224 = constructorAssetFree c (i + 1) := by
    unfold constructorAssetFree; omega
  simp only [constructorAssetAllocationGuard hfree, hnext] at r4
  split
  · rename_i hfit
    rw [if_pos hfit, constructorAssetAllocationEnd hfree, hnext] at r4
    obtain ⟨_, _, _, r4⟩ := r4
    let allocated := writeWord (constructorAssetLoopMemory c i) 64
      (UInt256.ofNat (constructorAssetFree c (i + 1)))
    have hp : MemoryPrefix (constructorAssetLoopMemory c i) allocated (constructorRecordBase c) :=
      memoryPrefix_sparse_writeWord _ _ _ _ (Or.inr (by decide))
    have hin : 1664 + 224 * i + 224 ≤ allocated.size := by
      have hs := le_trans (constructorAssetLoopMemory_prefix c i).size hp.size
      rw [constructorCopiedMemory_size] at hs
      omega
    have hread (j : Nat) (hj : j < 7) :
        memLoad (UInt256.ofNat (1664 + 224 * i + 32 * j)) allocated =
          c.assetConfigs[i].word j := by
      rw [memoryPrefix_load hp (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)
        (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; unfold constructorRecordBase; omega)
        (by
          have hs := (constructorAssetLoopMemory_prefix c i).size
          rw [constructorCopiedMemory_size] at hs
          rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)]
      exact constructorAssetLoopMemory_load hi hj hsize
    obtain ⟨aw5, k5, C5, r5⟩ := cometConstructorAssetFields
      (by change 17 ≤ 1024; decide) (by omega)
      (by
        unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase
        omega) hin
      (by rw [hnext]; change _ < 2^256; omega) hread r4
    have hentry : (UInt256.ofNat (constructorAssetEntry c i)).toNat = constructorAssetEntry c i :=
      UInt256.toNat_ofNat_of_lt (by
        unfold constructorAssetEntry constructorAssetFree constructorArrayEnd at *
        change _ < 2^256; omega)
    have hentryNext : UInt256.ofNat (constructorAssetEntry c i) + ⟨32⟩ =
        UInt256.ofNat (constructorAssetEntry c (i + 1)) := by
      apply u256_inj
      rw [uadd_toNat, hentry]
      change (constructorAssetEntry c i + 32) % UInt256.size = _
      rw [show constructorAssetEntry c i + 32 = constructorAssetEntry c (i + 1) by
        unfold constructorAssetEntry; omega]
      rfl
    have hsrcNext : UInt256.ofNat (1664 + 224 * i) + ⟨224⟩ =
        UInt256.ofNat (1664 + 224 * (i + 1)) := by
      apply u256_inj
      rw [uadd_toNat, hsrc]
      change (1664 + 224 * i + 224) % UInt256.size = _
      rw [show 1664 + 224 * i + 224 = 1664 + 224 * (i + 1) by omega]
      rfl
    rw [hentry, hentryNext, hsrcNext] at r5
    refine ⟨aw5, k5, C5, ?_⟩
    simpa only [constructorAssetLoopStack, constructorAssetLoopMemory, dif_pos hi,
      constructorAssetStoreMemory, hnext] using r5
  · rename_i hfit
    rw [if_neg hfit] at r4
    exact r4

theorem cometConstructorAssetExit {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig}
    {aw : UInt256} {k C : Nat}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨664⟩ (constructorAssetLoopStack c c.assetConfigs.length)
      (constructorAssetLoopMemory c c.assetConfigs.length) aw ByteArray.empty σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨685⟩ (constructorAssetLoopStack c c.assetConfigs.length)
      (constructorAssetLoopMemory c c.assetConfigs.length) aw' ByteArray.empty σ k' C' := by
  have r := cometWithExtendedAssetListCreation_block_664_fallthrough
    (by change 14 ≤ 1024; decide) (by
      apply ult_zero
      change (constructorAssetsDataEnd c).toNat ≤ _
      rw [constructorAssetsDataEnd_toNat hsize, UInt256.toNat_ofNat_of_lt (by omega)]
      rfl) h
  exact ⟨_, _, _, r⟩

/-- Iterate over every encoded asset; a failed allocation ends in the revert/OOG relation. -/
theorem cometConstructorAssetLoop {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig} {i : Nat}
    {aw : UInt256} {k C : Nat}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (hi : i ≤ c.assetConfigs.length) (hfree : constructorAssetFree c i < 2^64)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨664⟩ (constructorAssetLoopStack c i)
      (constructorAssetLoopMemory c i) aw ByteArray.empty σ k C) :
    if constructorAssetFree c c.assetConfigs.length < 2^64 then
      ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
        (initState σ σ₀ g A I) ⟨685⟩ (constructorAssetLoopStack c c.assetConfigs.length)
        (constructorAssetLoopMemory c c.assetConfigs.length) aw' ByteArray.empty σ k' C'
    else RDrev (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) g
      (initState σ σ₀ g A I) := by
  induction hremaining : c.assetConfigs.length - i generalizing i aw k C with
  | zero =>
    have he : i = c.assetConfigs.length := by omega
    subst i
    rw [if_pos hfree]
    exact cometConstructorAssetExit hsize h
  | succ remaining ih =>
    have hi' : i < c.assetConfigs.length := by omega
    have step := cometConstructorAssetStep hsize hi' hfree h
    by_cases hnext : constructorAssetFree c (i + 1) < 2^64
    · rw [if_pos hnext] at step
      obtain ⟨_, _, _, hstep⟩ := step
      exact ih (by omega) hnext hstep (by omega)
    · rw [if_neg hnext] at step
      have hfinal : ¬ constructorAssetFree c c.assetConfigs.length < 2^64 := by
        unfold constructorAssetFree at *
        omega
      rw [if_neg hfinal]
      exact step

/-- The complete constructor argument-decoding trace. -/
theorem cometConstructorDecode {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig}
    (hcode : I.code = cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
    (hv : I.weiValue = ⟨0⟩) (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    if constructorAssetFree c c.assetConfigs.length < 2^64 then
      ∃ aw k C, RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
        (initState σ σ₀ g A I) ⟨685⟩ (constructorAssetLoopStack c c.assetConfigs.length)
        (constructorAssetLoopMemory c c.assetConfigs.length) aw ByteArray.empty σ k C
    else RDrev (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) g
      (initState σ σ₀ g A I) := by
  have head := cometConstructorDecodeToAssets (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hv hsize
  by_cases harray : constructorArrayEnd c < 2^64
  · rw [if_pos harray] at head
    obtain ⟨_, _, _, hhead⟩ := head
    exact cometConstructorAssetLoop hsize (Nat.zero_le _) harray hhead
  · rw [if_neg harray] at head
    have hfinal : ¬ constructorAssetFree c c.assetConfigs.length < 2^64 := by
      unfold constructorAssetFree; omega
    rw [if_neg hfinal]
    exact head

end Benchmarks.CompoundIII.Comet

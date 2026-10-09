import Benchmarks.CompoundIII.Comet.ConstructorDecodeHead

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

def constructorAllocationGuard (ptr len : UInt256) : UInt256 :=
  UInt256.lor (UInt256.lt (allocationEnd ptr len) ptr)
    (UInt256.gt (allocationEnd ptr len) (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨64⟩) ⟨1⟩))

theorem cometCreationAllocate {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr len ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (hret : (D_J cometWithExtendedAssetListCreationBytecode 0).contains ret = true)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨2711⟩
      (ptr :: len :: ret :: R) mem aw rdata σ k C) :
    if constructorAllocationGuard ptr len = ⟨0⟩ then
      ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ret R
        (writeWord mem 64 (allocationEnd ptr len)) aw' rdata σ k' C'
    else RDrev (cometWithExtendedAssetListCreationBytecode ++ tail) g s0 := by
  split
  · rename_i hg
    have r1 := cometWithExtendedAssetListCreation_block_2711_fallthrough
      (by change R.length + 1 + 5 ≤ 1024; omega) hg h
    have r2 := cometWithExtendedAssetListCreation_block_2743 (by omega) hret r1
    exact ⟨_, _, _, r2⟩
  · rename_i hg
    have r1 := cometWithExtendedAssetListCreation_block_2711_taken
      (by change R.length + 1 + 5 ≤ 1024; omega) hg (by native_decide) h
    exact cometWithExtendedAssetListCreation_block_2689
      (by change R.length + 2 + 2 ≤ 1024; omega) r1

def constructorRecordBase (c : ConstructorConfig) : Nat := 1664 + 224 * c.assetConfigs.length

def constructorRecordMemory (c : ConstructorConfig) : ByteArray :=
  writeWord (constructorCopiedMemory c) 64 (UInt256.ofNat (constructorRecordBase c + 672))

theorem constructorRecordAllocationEnd {c : ConstructorConfig}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    allocationEnd (UInt256.ofNat (constructorRecordBase c)) ⟨672⟩ =
      UInt256.ofNat (constructorRecordBase c + 672) := by
  change UInt256.ofNat (constructorRecordBase c) + ⟨672⟩ = _
  apply u256_inj
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by unfold constructorRecordBase; omega)]
  change (constructorRecordBase c + 672) % UInt256.size = _
  rfl

theorem constructorRecordAllocationGuard {c : ConstructorConfig}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    constructorAllocationGuard (UInt256.ofNat (constructorRecordBase c)) ⟨672⟩ = ⟨0⟩ ↔
      constructorRecordBase c + 672 < 2^64 := by
  have hbase : (UInt256.ofNat (constructorRecordBase c)).toNat = constructorRecordBase c :=
    UInt256.toNat_ofNat_of_lt (by unfold constructorRecordBase; omega)
  have hend : (UInt256.ofNat (constructorRecordBase c + 672)).toNat =
      constructorRecordBase c + 672 :=
    UInt256.toNat_ofNat_of_lt (by unfold constructorRecordBase; omega)
  rw [constructorAllocationGuard, constructorRecordAllocationEnd hsize,
    ult_zero (by rw [hbase, hend]; omega)]
  by_cases hs : constructorRecordBase c + 672 < 2^64
  · rw [ugt_zero (by rw [hend]; change _ ≤ 2^64 - 1; omega)]
    exact ⟨fun _ ↦ hs, fun _ ↦ rfl⟩
  · rw [ugt_one (by rw [hend]; change 2^64 - 1 < _; omega)]
    exact ⟨fun h ↦ False.elim ((by decide : UInt256.lor ⟨0⟩ ⟨1⟩ ≠ ⟨0⟩) h),
      fun h ↦ False.elim (hs h)⟩

set_option maxRecDepth 2000 in
theorem cometConstructorRecordAllocate {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig}
    {aw : UInt256} {k C : Nat}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨2711⟩
      [UInt256.ofNat (constructorRecordBase c), ⟨672⟩, ⟨99⟩, ⟨928⟩, ⟨32⟩,
        constructorArgumentSizeWord c, UInt256.ofNat (constructorRecordBase c)]
      (constructorCopiedMemory c) aw ByteArray.empty σ k C) :
    if constructorRecordBase c + 672 < 2^64 then
      ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
        (initState σ σ₀ g A I) ⟨99⟩
        [⟨928⟩, ⟨32⟩, constructorArgumentSizeWord c, UInt256.ofNat (constructorRecordBase c)]
        (constructorRecordMemory c) aw' ByteArray.empty σ k' C'
    else RDrev (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) g
      (initState σ σ₀ g A I) := by
  have hr := cometCreationAllocate (by change 10 ≤ 1024; decide) (by native_decide) h
  simpa only [constructorRecordAllocationGuard hsize, constructorRecordAllocationEnd hsize,
    constructorRecordMemory] using hr

end Benchmarks.CompoundIII.Comet

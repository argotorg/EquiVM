import Benchmarks.CompoundIII.Comet.ConstructorAssetHeader

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def constructorArrayBase (c : ConstructorConfig) : Nat := constructorRecordBase c + 672

def constructorArrayEnd (c : ConstructorConfig) : Nat :=
  constructorArrayBase c + 32 + 32 * c.assetConfigs.length

def constructorArrayMemory (c : ConstructorConfig) : ByteArray :=
  writeWord (constructorScalarMemory c 20) 64 (UInt256.ofNat (constructorArrayEnd c))

theorem constructorArrayAllocationEnd_toNat {c : ConstructorConfig}
    (hrecord : constructorRecordBase c + 672 < 2^64) :
    (allocationEnd (UInt256.ofNat (constructorArrayBase c))
      (UInt256.ofNat (32 + 32 * c.assetConfigs.length))).toNat = constructorArrayEnd c := by
  have hn : c.assetConfigs.length < 2^64 := by unfold constructorRecordBase at hrecord; omega
  have hp : (UInt256.ofNat (constructorArrayBase c)).toNat = constructorArrayBase c :=
    UInt256.toNat_ofNat_of_lt (by unfold constructorArrayBase; change _ < 2^256; omega)
  have hl : (UInt256.ofNat (32 + 32 * c.assetConfigs.length)).toNat =
      32 + 32 * c.assetConfigs.length :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hadd : (UInt256.ofNat (32 + 32 * c.assetConfigs.length) + (⟨31⟩ : UInt256)).toNat =
      63 + 32 * c.assetConfigs.length := by
    rw [uadd_toNat, hl]
    change (32 + 32 * c.assetConfigs.length + 31) % UInt256.size = _
    rw [Nat.mod_eq_of_lt (by change _ < 2^256; omega)]
    omega
  rw [allocationEnd, uadd_toNat, hp, u256_land_comm, longDataCutoff_toNat, hadd]
  have hround : (63 + 32 * c.assetConfigs.length) / 32 * 32 =
      32 + 32 * c.assetConfigs.length := by omega
  rw [hround, Nat.mod_eq_of_lt (by
    unfold constructorArrayBase; change _ < 2^256; omega)]
  unfold constructorArrayEnd
  omega

theorem constructorArrayEnd_small {c : ConstructorConfig}
    (hrecord : constructorRecordBase c + 672 < 2^64) : constructorArrayEnd c < UInt256.size := by
  unfold constructorArrayEnd constructorArrayBase constructorRecordBase at *
  change _ < 2^256
  omega

theorem constructorArrayAllocationEnd {c : ConstructorConfig}
    (hrecord : constructorRecordBase c + 672 < 2^64) :
    allocationEnd (UInt256.ofNat (constructorArrayBase c))
      (UInt256.ofNat (32 + 32 * c.assetConfigs.length)) =
        UInt256.ofNat (constructorArrayEnd c) := by
  apply u256_inj
  rw [constructorArrayAllocationEnd_toNat hrecord,
    UInt256.toNat_ofNat_of_lt (constructorArrayEnd_small hrecord)]

-- LIBRARY CANDIDATE: the allocator's upper-bound test when its end does not wrap below its start.
theorem constructorAllocationGuard_iff {ptr len : UInt256} {endPos : Nat}
    (hend : (allocationEnd ptr len).toNat = endPos) (hle : ptr.toNat ≤ endPos) :
    constructorAllocationGuard ptr len = ⟨0⟩ ↔ endPos < 2^64 := by
  rw [constructorAllocationGuard, ult_zero (by rw [hend]; exact hle)]
  by_cases hs : endPos < 2^64
  · rw [ugt_zero (by rw [hend]; change _ ≤ 2^64 - 1; omega)]
    exact ⟨fun _ ↦ hs, fun _ ↦ rfl⟩
  · rw [ugt_one (by rw [hend]; change 2^64 - 1 < _; omega)]
    exact ⟨fun h ↦ False.elim ((by decide : UInt256.lor ⟨0⟩ ⟨1⟩ ≠ ⟨0⟩) h),
      fun h ↦ False.elim (hs h)⟩

theorem constructorArrayAllocationGuard {c : ConstructorConfig}
    (hrecord : constructorRecordBase c + 672 < 2^64) :
    constructorAllocationGuard (UInt256.ofNat (constructorArrayBase c))
      (UInt256.ofNat (32 + 32 * c.assetConfigs.length)) = ⟨0⟩ ↔
        constructorArrayEnd c < 2^64 := by
  apply constructorAllocationGuard_iff (constructorArrayAllocationEnd_toNat hrecord)
  rw [UInt256.toNat_ofNat_of_lt (by
    unfold constructorArrayBase; change _ < 2^256; omega)]
  unfold constructorArrayEnd
  omega

theorem cometConstructorArrayAllocate {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig}
    {aw : UInt256} {k C : Nat} (hrecord : constructorRecordBase c + 672 < 2^64)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨2711⟩
      [UInt256.ofNat (constructorArrayBase c), UInt256.ofNat (32 + 32 * c.assetConfigs.length),
        ⟨623⟩, ⟨672⟩, ⟨928⟩, constructorArgumentSizeWord c, UInt256.ofNat c.assetConfigs.length,
        ⟨32⟩, UInt256.ofNat (constructorArrayBase c), UInt256.ofNat (constructorRecordBase c)]
      (constructorScalarMemory c 20) aw ByteArray.empty σ k C) :
    if constructorArrayEnd c < 2^64 then
      ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
        (initState σ σ₀ g A I) ⟨623⟩
        [⟨672⟩, ⟨928⟩, constructorArgumentSizeWord c, UInt256.ofNat c.assetConfigs.length,
          ⟨32⟩, UInt256.ofNat (constructorArrayBase c), UInt256.ofNat (constructorRecordBase c)]
        (constructorArrayMemory c) aw' ByteArray.empty σ k' C'
    else RDrev (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) g
      (initState σ σ₀ g A I) := by
  have hr := cometCreationAllocate (by change 13 ≤ 1024; decide) (by native_decide) h
  simpa only [constructorArrayAllocationGuard hrecord, constructorArrayAllocationEnd hrecord,
    constructorArrayMemory] using hr

end Benchmarks.CompoundIII.Comet

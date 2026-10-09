import Benchmarks.CompoundIII.Comet.ConstructorDecimalsMemory
import Benchmarks.CompoundIII.Comet.CreationBlocks_005
import Benchmarks.CompoundIII.Comet.CreationBlocks_006

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometCreationAllocateSmall {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw ptr len ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hlen : len.toNat ≤ 32) (hptr : ptr.toNat + 32 < 2^64)
    (hret : (D_J cometWithExtendedAssetListCreationBytecode 0).contains ret = true)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨2711⟩
      (ptr :: len :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ret R
      (writeWord mem 64 (allocationEnd ptr len)) aw' rdata σ k' C' := by
  have hg : constructorAllocationGuard ptr len = ⟨0⟩ :=
    allocationEnd_bounded_guard (bound := 1) hlen hptr
  simpa only [if_pos hg] using cometCreationAllocate hstack hret h

/-- Decode the first decimals response, including failed calls, short data and dirty uint8 words. -/
theorem cometConstructorDecimalsResponse {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {σ : AccountMap} {c : ConstructorConfig} {out : ByteArray} {z : Bool}
    {aw : UInt256} {k C : Nat}
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64) (hhi : out.size < 2^138)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) ee g s0 ⟨734⟩
      ((if z then ⟨1⟩ else ⟨0⟩) ::
        UInt256.ofNat (constructorAssetFree c c.assetConfigs.length) ::
        UInt256.ofNat (constructorRecordBase c) ::
        constructorAssetLoopStack c c.assetConfigs.length)
      (constructorDecimalsCopyMemory c out) aw out σ k C) :
    if z = true ∧ DecimalsReturnValid out then
      ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
        ee g s0 ⟨750⟩
        (⟨672⟩ :: calldataWord out 0 :: UInt256.ofNat (constructorRecordBase c) ::
          constructorAssetLoopStack c c.assetConfigs.length)
        (constructorDecimalsReturnMemory c out) aw' out σ k' C'
    else RDrev (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) g s0 := by
  have hsize : out.size < UInt256.size := by change _ < 2^256; omega
  have hout : (UInt256.ofNat out.size).toNat = out.size := UInt256.toNat_ofNat_of_lt hsize
  have hp : (UInt256.ofNat (constructorAssetFree c c.assetConfigs.length)).toNat =
      constructorAssetFree c c.assetConfigs.length :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hfit : (UInt256.ofNat (constructorAssetFree c c.assetConfigs.length)).toNat + 32 < 2^64 := by
    rw [hp]; exact constructorDecimalsAllocation_fits hfree
  have hsub (n : Nat) (hn : n ≤ 32) :
      UInt256.sub (UInt256.ofNat (constructorAssetFree c c.assetConfigs.length) + UInt256.ofNat n)
        (UInt256.ofNat (constructorAssetFree c c.assetConfigs.length)) = UInt256.ofNat n :=
    usub_uadd_lit_cancel (by change _ < 2^256; omega) (by change _ < 2^256; omega)
      (by rw [hp] at hfit; change _ < 2^256; omega)
  cases z with
  | false =>
    rw [if_neg (by simp)]
    have r1 := cometWithExtendedAssetListCreation_block_734_taken
      (by change 14 ≤ 1024; decide) (by decide) (by native_decide) h
    exact cometWithExtendedAssetListCreation_block_2063 (by change 16 ≤ 1024; decide)
      (by rw [hout]; change 0 + out.size ≤ out.size; omega) r1
  | true =>
    have r1 := cometWithExtendedAssetListCreation_block_734_fallthrough
      (by change 14 ≤ 1024; decide) (by decide) h
    have r2 := cometWithExtendedAssetListCreation_block_742_taken
      (by change 14 ≤ 1024; decide) (by decide) (by native_decide) r1
    by_cases hlo : 32 ≤ out.size
    · have r3 := cometWithExtendedAssetListCreation_block_2428_fallthrough
        (by change 16 ≤ 1024; decide) (by apply ugt_zero; rw [hout]; exact hlo) r2
      have r4 := cometWithExtendedAssetListCreation_block_2442
        (by change 19 ≤ 1024; decide) (by native_decide) r3
      obtain ⟨_, _, _, r5⟩ := cometCreationAllocateSmall
        (by change 21 ≤ 1024; decide) (by decide) hfit (by native_decide) r4
      have hend : allocationEnd (UInt256.ofNat (constructorAssetFree c c.assetConfigs.length))
          (UInt256.ofNat 32) =
          UInt256.ofNat (constructorAssetFree c c.assetConfigs.length + 32) := by
        apply u256_inj
        rw [allocationEnd_bounded_toNat (bound := 1) (by decide) hfit, hp]
        rw [UInt256.toNat_ofNat_of_lt
          (show constructorAssetFree c c.assetConfigs.length + 32 < UInt256.size by
            rw [hp] at hfit; change _ < 2^256; omega)]
        rfl
      rw [hend] at r5
      have r6 := cometWithExtendedAssetListCreation_block_2457_fallthrough
        (by change 16 ≤ 1024; decide) (by
          rw [hsub 32 (by omega)]
          exact slt_ofNat_lit_zero (by decide) (by decide) (by decide)) r5
      have r7 := cometWithExtendedAssetListCreation_block_2467
        (by change 13 ≤ 1024; decide) (by native_decide) r6
      have hread : memLoad (UInt256.ofNat (constructorAssetFree c c.assetConfigs.length))
          (constructorDecimalsReturnMemory c out) = calldataWord out 0 :=
        constructorDecimalsReturnMemory_word hfree hlo hsize
      change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) ee g s0
        ⟨2810⟩ (UInt256.ofNat (constructorAssetFree c c.assetConfigs.length) :: ⟨2478⟩ ::
          UInt256.ofNat (constructorRecordBase c) ::
          constructorAssetLoopStack c c.assetConfigs.length)
        (constructorDecimalsReturnMemory c out) _ out σ _ _ at r7
      by_cases hcanon : (calldataWord out 0).toNat < 2^8
      · rw [if_pos ⟨rfl, hlo, hcanon⟩]
        obtain ⟨_, _, _, r8⟩ := cometCreationReadUint8
          (by change 14 ≤ 1024; decide) hread hcanon (by native_decide) r7
        have r9 := cometWithExtendedAssetListCreation_block_2478
          (by change 13 ≤ 1024; decide) (by native_decide) r8
        exact ⟨_, _, _, r9⟩
      · rw [if_neg (fun hh ↦ hcanon hh.2.2)]
        have r8 := cometWithExtendedAssetListCreation_block_2810_taken
          (by change 14 ≤ 1024; decide) (by
            rw [hread]
            apply u256_sub_ne_zero_of_ne
            intro he
            exact hcanon ((lowByteClean_iff _).mp he.symm)) (by native_decide) r7
        exact cometWithExtendedAssetListCreation_block_2684 (by change 14 ≤ 1024; decide) r8
    · rw [if_neg (fun hh ↦ hlo hh.2.1)]
      have r3 := cometWithExtendedAssetListCreation_block_2428_taken
        (by change 16 ≤ 1024; decide) (by
          rw [ugt_one (by rw [hout]; change out.size < 32; omega)]; decide)
        (by native_decide) r2
      have r4 := cometWithExtendedAssetListCreation_block_2485
        (by change 15 ≤ 1024; decide) (by native_decide) r3
      have r5 := cometWithExtendedAssetListCreation_block_2442
        (by change 19 ≤ 1024; decide) (by native_decide) r4
      obtain ⟨_, _, _, r6⟩ := cometCreationAllocateSmall
        (by change 21 ≤ 1024; decide) (by rw [hout]; omega) hfit (by native_decide) r5
      have r7 := cometWithExtendedAssetListCreation_block_2457_taken
        (by change 16 ≤ 1024; decide) (by
          rw [hsub out.size (by omega), slt_ofNat_lit_one_low (by decide) (by omega)]; decide)
        (by native_decide) r6
      exact cometWithExtendedAssetListCreation_block_2273 (by change 13 ≤ 1024; decide) r7

end Benchmarks.CompoundIII.Comet

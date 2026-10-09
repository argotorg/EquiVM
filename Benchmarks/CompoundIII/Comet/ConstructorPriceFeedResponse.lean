import Benchmarks.CompoundIII.Comet.ConstructorPriceFeedCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometConstructorPriceFeedResponse {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {σ : AccountMap} {c : ConstructorConfig} {out feed : ByteArray} {z : Bool}
    {aw : UInt256} {k C : Nat}
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64)
    (hout : out.size < UInt256.size) (hhi : feed.size < 2^138)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) ee g s0 ⟨872⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: constructorPriceFeedPtr c :: calldataWord out 0 ::
        UInt256.ofNat (constructorRecordBase c) ::
        constructorAssetLoopStack c c.assetConfigs.length)
      (constructorPriceFeedCopyMemory c out feed) aw feed σ k C) :
    if z = true ∧ DecimalsReturnValid feed then
      ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
        ee g s0 ⟨888⟩
        (⟨255⟩ :: calldataWord feed 0 :: calldataWord out 0 ::
          UInt256.ofNat (constructorRecordBase c) ::
          constructorAssetLoopStack c c.assetConfigs.length)
        (constructorPriceFeedReturnMemory c out feed) aw' feed σ k' C'
    else RDrev (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) g s0 := by
  have hsize : feed.size < UInt256.size := by change _ < 2^256; omega
  have hfeed : (UInt256.ofNat feed.size).toNat = feed.size := UInt256.toNat_ofNat_of_lt hsize
  have hfit := constructorPriceFeedPtr_fits hfree
  have hsub (n : Nat) (hn : n ≤ 32) :
      UInt256.sub (constructorPriceFeedPtr c + UInt256.ofNat n) (constructorPriceFeedPtr c) =
        UInt256.ofNat n := by
    apply usub_uadd_lit_cancel (by change _ < 2^256; omega) (by change _ < 2^256; omega)
    change constructorAssetFree c c.assetConfigs.length + 32 + n < 2^256
    rw [constructorPriceFeedPtr_toNat hfree] at hfit
    omega
  cases z with
  | false =>
    rw [if_neg (by simp)]
    have r1 := cometWithExtendedAssetListCreation_block_872_taken
      (by change 15 ≤ 1024; decide) (by decide) (by native_decide) h
    exact cometWithExtendedAssetListCreation_block_2063 (by change 17 ≤ 1024; decide)
      (by rw [hfeed]; change 0 + feed.size ≤ feed.size; omega) r1
  | true =>
    have r1 := cometWithExtendedAssetListCreation_block_872_fallthrough
      (by change 15 ≤ 1024; decide) (by decide) h
    have r2 := cometWithExtendedAssetListCreation_block_880_taken
      (by change 15 ≤ 1024; decide) (by decide) (by native_decide) r1
    by_cases hlo : 32 ≤ feed.size
    · have r3 := cometWithExtendedAssetListCreation_block_2303_fallthrough
        (by change 17 ≤ 1024; decide) (by apply ugt_zero; rw [hfeed]; exact hlo) r2
      have r4 := cometWithExtendedAssetListCreation_block_2317
        (by change 20 ≤ 1024; decide) (by native_decide) r3
      obtain ⟨_, _, _, r5⟩ := cometCreationAllocateSmall
        (by change 22 ≤ 1024; decide) (by decide) hfit (by native_decide) r4
      have hend : allocationEnd (constructorPriceFeedPtr c) (UInt256.ofNat 32) =
          UInt256.ofNat (constructorAssetFree c c.assetConfigs.length + 64) := by
        apply u256_inj
        rw [allocationEnd_bounded_toNat (bound := 1) (by decide) hfit,
          constructorPriceFeedPtr_toNat hfree]
        rw [UInt256.toNat_ofNat_of_lt
          (show constructorAssetFree c c.assetConfigs.length + 64 < UInt256.size by
            rw [constructorPriceFeedPtr_toNat hfree] at hfit; change _ < 2^256; omega)]
        change constructorAssetFree c c.assetConfigs.length + 32 + 32 = _
        omega
      rw [hend] at r5
      have r6 := cometWithExtendedAssetListCreation_block_2332_fallthrough
        (by change 17 ≤ 1024; decide) (by
          rw [hsub 32 (by omega)]
          exact slt_ofNat_lit_zero (by decide) (by decide) (by decide)) r5
      have r7 := cometWithExtendedAssetListCreation_block_2342
        (by change 16 ≤ 1024; decide) (by native_decide) r6
      have hread := constructorPriceFeedReturnMemory_word hfree hout hsize hlo
      change RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) ee g s0
        ⟨2810⟩ (constructorPriceFeedPtr c :: ⟨2357⟩ :: ⟨255⟩ :: ⟨8⟩ :: calldataWord out 0 ::
          UInt256.ofNat (constructorRecordBase c) ::
          constructorAssetLoopStack c c.assetConfigs.length)
        (constructorPriceFeedReturnMemory c out feed) _ feed σ _ _ at r7
      by_cases hcanon : (calldataWord feed 0).toNat < 2^8
      · rw [if_pos ⟨rfl, hlo, hcanon⟩]
        obtain ⟨_, _, _, r8⟩ := cometCreationReadUint8
          (by change 17 ≤ 1024; decide) hread hcanon (by native_decide) r7
        have r9 := cometWithExtendedAssetListCreation_block_2357
          (by change 14 ≤ 1024; decide) (by native_decide) r8
        exact ⟨_, _, _, r9⟩
      · rw [if_neg (fun hh ↦ hcanon hh.2.2)]
        have r8 := cometWithExtendedAssetListCreation_block_2810_taken
          (by change 17 ≤ 1024; decide) (by
            rw [hread]
            apply u256_sub_ne_zero_of_ne
            intro he
            exact hcanon ((lowByteClean_iff _).mp he.symm)) (by native_decide) r7
        exact cometWithExtendedAssetListCreation_block_2684 (by change 17 ≤ 1024; decide) r8
    · rw [if_neg (fun hh ↦ hlo hh.2.1)]
      have r3 := cometWithExtendedAssetListCreation_block_2303_taken
        (by change 17 ≤ 1024; decide) (by
          rw [ugt_one (by rw [hfeed]; change feed.size < 32; omega)]; decide)
        (by native_decide) r2
      have r4 := cometWithExtendedAssetListCreation_block_2365
        (by change 16 ≤ 1024; decide) (by native_decide) r3
      have r5 := cometWithExtendedAssetListCreation_block_2317
        (by change 20 ≤ 1024; decide) (by native_decide) r4
      obtain ⟨_, _, _, r6⟩ := cometCreationAllocateSmall
        (by change 22 ≤ 1024; decide) (by rw [hfeed]; omega) hfit (by native_decide) r5
      have r7 := cometWithExtendedAssetListCreation_block_2332_taken
        (by change 17 ≤ 1024; decide) (by
          rw [hsub feed.size (by omega), slt_ofNat_lit_one_low (by decide) (by omega)]; decide)
        (by native_decide) r6
      exact cometWithExtendedAssetListCreation_block_2273 (by change 14 ≤ 1024; decide) r7

end Benchmarks.CompoundIII.Comet

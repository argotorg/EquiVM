import Benchmarks.CompoundIII.Comet.AssetChecks
import Benchmarks.CompoundIII.Comet.AssetCallMemory
import Benchmarks.CompoundIII.Comet.MemoryAllocate
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_037
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_014
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_038

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometAssetCallFailed {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨7265⟩ (⟨0⟩ :: ⟨256⟩ :: ptr :: ret :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_7265_taken
    (immWords := wordsOf (immStore v)) (by dsimp only [List.length_cons]; omega)
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_7469
    (immWords := wordsOf (immStore v)) (by change R.length + 4 + 2 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  exact cometWithExtendedAssetList_block_7166 (immWords := wordsOf (immStore v))
    (by change R.length + 4 + 4 ≤ 1024; omega)
    (by change 0 + out.size % UInt256.size ≤ out.size; simpa using Nat.mod_le out.size _) r2

theorem cometAssetResponseStart {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨7265⟩ (⟨1⟩ :: ⟨256⟩ :: ptr :: ret :: R)
      mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨7284⟩ (ptr :: ⟨256⟩ :: ⟨0⟩ :: ret :: R)
      mem aw out σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_7265_fallthrough
    (immWords := wordsOf (immStore v)) (by dsimp only [List.length_cons]; omega)
    (by decide) h
  have r2 := cometWithExtendedAssetList_block_7272_taken
    (immWords := wordsOf (immStore v)) (by dsimp only [List.length_cons]; omega)
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  exact ⟨_, _, r2⟩

theorem cometAssetResponseShort {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024) (hptr : ptr.toNat + 256 < 2^64)
    (hshort : out.size < 256)
    (h : RD (deployedRuntime v) ee g s0 ⟨7284⟩ (ptr :: ⟨256⟩ :: ⟨0⟩ :: ret :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hsize : out.size < UInt256.size := by change out.size < 2^256; omega
  have r1 := cometWithExtendedAssetList_block_7284_taken
    (immWords := wordsOf (immStore v)) (by dsimp only [List.length_cons]; omega)
    (by rw [ugt_one (by rw [UInt256.toNat_ofNat_of_lt hsize]; exact hshort)]; decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_7462
    (immWords := wordsOf (immStore v)) (by dsimp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_7297
    (immWords := wordsOf (immStore v)) (by dsimp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  obtain ⟨aw4, k4, C4, r4⟩ := cometAllocateBounded (v := v) (bound := 8)
    (by dsimp only [List.length_cons]; omega)
    (by rw [UInt256.toNat_ofNat_of_lt hsize]; omega) hptr
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  have r5 := cometWithExtendedAssetList_block_7307_taken
    (immWords := wordsOf (immStore v)) (by dsimp only [List.length_cons]; omega)
    (by rw [word_add_sub_left]
        change UInt256.slt (UInt256.ofNat out.size) (UInt256.ofNat 256) ≠ ⟨0⟩
        rw [slt_ofNat_lit_one_low (by decide) hshort]; decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
  exact cometWithExtendedAssetList_block_1938 (immWords := wordsOf (immStore v))
    (by dsimp only [List.length_cons]; omega) r5

theorem cometAssetResponseFull {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024) (hptr : ptr.toNat + 256 < 2^64)
    (hout : 256 ≤ out.size) (hhi : out.size < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 ⟨7284⟩ (ptr :: ⟨256⟩ :: ⟨0⟩ :: ret :: R)
      mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨7316⟩ (⟨0⟩ :: ptr :: ⟨256⟩ :: ret :: R)
      (writeWord mem 64 (ptr + ⟨256⟩)) aw' out σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_7284_fallthrough
    (immWords := wordsOf (immStore v)) (by dsimp only [List.length_cons]; omega)
    (ugt_zero (by rw [UInt256.toNat_ofNat_of_lt hhi]; exact hout)) h
  have r2 := cometWithExtendedAssetList_block_7297
    (immWords := wordsOf (immStore v)) (by dsimp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  obtain ⟨aw3, k3, C3, r3⟩ := cometAllocateBounded (v := v) (bound := 8)
    (by dsimp only [List.length_cons]; omega) (by decide) hptr
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
  rw [allocationEnd_256] at r3
  have r4 := cometWithExtendedAssetList_block_7307_fallthrough
    (immWords := wordsOf (immStore v)) (by dsimp only [List.length_cons]; omega)
    (by rw [word_add_sub_left]; decide) r3
  exact ⟨_, _, _, r4⟩

theorem cometAssetResponseAllocate {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024) (hptr : ptr.toNat + 512 < 2^64)
    (h : RD (deployedRuntime v) ee g s0 ⟨7316⟩ (⟨0⟩ :: ptr :: ⟨256⟩ :: ret :: R)
      (assetReserveMemory mem ptr out) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨7335⟩
      (ptr :: ⟨224⟩ :: ⟨7454⟩ :: (ptr + ⟨256⟩) :: ret :: R)
      (assetDecodeMemory mem ptr out) aw' out σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_7316
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [cometWithExtendedAssetList_block_7316_stack,
    show memLoad (UInt256.ofNat 64) (assetReserveMemory mem ptr out) = ptr + ⟨256⟩ from
      assetReserveMemory_free mem out ptr] at r1
  obtain ⟨aw2, k2, C2, r2⟩ := cometAllocateBounded (v := v) (bound := 8)
    (by change R.length + 5 + 6 ≤ 1024; omega) (by decide) (by
      have ha := uadd_word_ofNat_toNat ptr 256 (by change ptr.toNat + 256 < 2^256; omega)
      change (ptr + UInt256.ofNat 256).toNat + 32 * 8 < 2^64
      rw [ha]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  rw [allocationEnd_256] at r2
  exact ⟨_, _, _, r2⟩

theorem cometAssetResponse {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256} {z : Bool}
    (hstack : R.length + 13 ≤ 1024) (hlo : 96 ≤ ptr.toNat)
    (hin : ptr.toNat ≤ mem.size) (hptr : ptr.toNat + 512 < 2^64)
    (hhi : out.size < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7265⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨256⟩ :: ptr :: ret :: R)
      (assetCopyMemory mem ptr out) aw out σ k C) :
    if z = true ∧ AssetValid out then
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret ((ptr + ⟨256⟩) :: R)
        (assetStore (assetDecodeMemory mem ptr out) (ptr + ⟨256⟩) out 8) aw' out σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  cases z with
  | false =>
      rw [if_neg (by simp)]
      exact cometAssetCallFailed (v := v) (by omega) h
  | true =>
      obtain ⟨k1, C1, r1⟩ := cometAssetResponseStart (v := v) (by omega) h
      by_cases hout : 256 ≤ out.size
      · obtain ⟨aw2, k2, C2, r2⟩ := cometAssetResponseFull (v := v) hstack
          (by omega) hout hhi r1
        obtain ⟨aw3, k3, C3, r3⟩ := cometAssetResponseAllocate (v := v) hstack hptr r2
        have ha : (ptr + (⟨256⟩ : UInt256)).toNat = ptr.toNat + 256 :=
          uadd_word_ofNat_toNat ptr 256 (by change ptr.toNat + 256 < 2^256; omega)
        have hf := cometAssetChecks (v := v) (by omega) hlo
          (by rw [assetDecodeMemory_size hlo hin hout hhi]; omega) (by rw [ha])
          (by rw [ha]; change ptr.toNat + 256 + 256 < 2^256; omega) hret
          (fun off ho ↦ assetDecodeMemory_word off ho hlo hin
            (by change ptr.toNat + 256 < 2^256; omega) hout hhi) r3
        simpa only [AssetValid, hout, true_and] using hf
      · rw [if_neg (by rintro ⟨_, hv⟩; exact hout hv.1)]
        exact cometAssetResponseShort (v := v) hstack (by omega) (Nat.lt_of_not_ge hout) r1

end Benchmarks.CompoundIII.Comet

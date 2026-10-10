import Benchmarks.CompoundIII.Comet.PriceChecks
import Benchmarks.CompoundIII.Comet.PriceMemory
import Benchmarks.CompoundIII.Comet.MemoryAllocate
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_037
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_014

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometPriceCallFailed {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨9411⟩ (⟨0⟩ :: ptr :: ret :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_9411_taken
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_9533
    (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  exact cometWithExtendedAssetList_block_7166 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 4 ≤ 1024; omega)
    (by change 0 + out.size % UInt256.size ≤ out.size; simpa using Nat.mod_le out.size _) r2

theorem cometPriceResponseStart {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨9411⟩ (⟨1⟩ :: ptr :: ret :: R)
      mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨9457⟩ (ptr :: ⟨0⟩ :: ret :: R)
      mem aw out σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_9411_fallthrough
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
    (by decide) h
  have r2 := cometWithExtendedAssetList_block_9418_taken
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  exact ⟨_, _, r2⟩

theorem cometPriceResponseShort {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hptr : ptr.toNat + 160 < 2^64)
    (hshort : out.size < 160)
    (h : RD (deployedRuntime v) ee g s0 ⟨9457⟩ (ptr :: ⟨0⟩ :: ret :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hsize : out.size < UInt256.size := by change out.size < 2^256; omega
  have r1 := cometWithExtendedAssetList_block_9457_taken
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
    (by rw [ugt_one (by rw [UInt256.toNat_ofNat_of_lt hsize]; exact hshort)]; decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_9525
    (immWords := wordsOf (immStore v)) (by change R.length + 3 + 3 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_9469
    (immWords := wordsOf (immStore v)) (by change R.length + 3 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  obtain ⟨aw4, k4, C4, r4⟩ := cometAllocate160 (v := v)
    (by change R.length + 6 + 6 ≤ 1024; omega)
    (by rw [UInt256.toNat_ofNat_of_lt hsize]; omega) hptr
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  have r5 := cometWithExtendedAssetList_block_9482_taken
    (immWords := wordsOf (immStore v)) (by change R.length + 3 + 4 ≤ 1024; omega)
    (by rw [word_add_sub_left, slt_ofNat_lit_one_low (by decide) hshort]; decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
  exact cometWithExtendedAssetList_block_1938 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 2 ≤ 1024; omega) r5

theorem cometPriceResponseFull {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hptr : ptr.toNat + 160 < 2^64)
    (hout : 160 ≤ out.size) (hhi : out.size < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 ⟨9457⟩ (ptr :: ⟨0⟩ :: ret :: R)
      mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨9491⟩ (⟨0⟩ :: ptr :: ret :: R)
      (writeWord mem 64 (ptr + ⟨160⟩)) aw' out σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_9457_fallthrough
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
    (ugt_zero (by rw [UInt256.toNat_ofNat_of_lt hhi]; exact hout)) h
  have r2 := cometWithExtendedAssetList_block_9469
    (immWords := wordsOf (immStore v)) (by change R.length + 3 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  obtain ⟨aw3, k3, C3, r3⟩ := cometAllocate160 (v := v)
    (by change R.length + 6 + 6 ≤ 1024; omega) (by decide) hptr
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
  rw [show allocationEnd ptr (UInt256.ofNat 160) = ptr + ⟨160⟩ from allocationEnd_160 ptr] at r3
  have r4 := cometWithExtendedAssetList_block_9482_fallthrough
    (immWords := wordsOf (immStore v)) (by change R.length + 3 + 4 ≤ 1024; omega)
    (by rw [word_add_sub_left]; decide) r3
  exact ⟨_, _, _, r4⟩

theorem cometPriceResponse {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256} {z : Bool}
    (hstack : R.length + 12 ≤ 1024) (hlo : 96 ≤ ptr.toNat)
    (hgap : ptr.toNat ≤ mem.size + 32) (hptr : ptr.toNat + 160 < 2^64)
    (hhi : out.size < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨9411⟩ ((if z then ⟨1⟩ else ⟨0⟩) :: ptr :: ret :: R)
      (priceCopyMemory mem ptr out) aw out σ k C) :
    if z = true ∧ PriceValid out then
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (calldataWord out 32 :: R)
        (priceReturnMemory mem ptr out) aw' out σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  cases z with
  | false =>
      rw [if_neg (by simp)]
      exact cometPriceCallFailed (v := v) (by omega) h
  | true =>
      obtain ⟨k1, C1, r1⟩ := cometPriceResponseStart (v := v) (by omega) h
      by_cases hout : 160 ≤ out.size
      · obtain ⟨aw2, k2, C2, r2⟩ := cometPriceResponseFull (v := v) hstack hptr hout hhi r1
        have hword := priceReturnMemory_word (mem := mem) (out := out) (ptr := ptr)
        have h0 : memLoad ptr (priceReturnMemory mem ptr out) = calldataWord out 0 := by
          simpa only [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by rfl, uint256_add_zero_right]
            using hword 0 (by decide) hlo hgap hptr hout hhi
        have hf := cometPriceChecks (v := v) (by omega) hret h0
          (hword 32 (by decide) hlo hgap hptr hout hhi)
          (hword 128 (by decide) hlo hgap hptr hout hhi) r2
        simpa only [PriceValid, hout, true_and] using hf
      · rw [if_neg (by rintro ⟨_, hv⟩; exact hout hv.1)]
        exact cometPriceResponseShort (v := v) hstack hptr (Nat.lt_of_not_ge hout) r1

end Benchmarks.CompoundIII.Comet

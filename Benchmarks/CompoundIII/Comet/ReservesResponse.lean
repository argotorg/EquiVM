import Benchmarks.CompoundIII.Comet.TokenBalanceResponse
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_047
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_048

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometReservesCallFailed {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr w1 supplyIndex borrowIndex : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨9950⟩
      (⟨0⟩ :: w1 :: supplyIndex :: borrowIndex :: ptr :: R) mem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_9950_taken
    (immWords := wordsOf (immStore v)) (by omega) (by decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_10116
    (immWords := wordsOf (immStore v)) (by change R.length + 5 + 2 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  exact cometWithExtendedAssetList_block_7166 (immWords := wordsOf (immStore v))
    (by change R.length + 5 + 4 ≤ 1024; omega)
    (by change 0 + out.size % UInt256.size ≤ out.size; simpa using Nat.mod_le out.size _) r2

theorem cometReservesResponseStart {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr w1 supplyIndex borrowIndex : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨9950⟩
      (⟨1⟩ :: w1 :: supplyIndex :: borrowIndex :: ptr :: R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨10060⟩
      (ptr :: w1 :: supplyIndex :: borrowIndex :: ⟨0⟩ :: R) mem aw out σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_9950_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by decide) h
  have r2 := cometWithExtendedAssetList_block_9957_taken
    (immWords := wordsOf (immStore v)) hstack (by decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  exact ⟨_, _, r2⟩

theorem cometReservesResponseShort {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr w1 supplyIndex borrowIndex : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024) (hptr : ptr.toNat + 32 < 2^64) (hshort : out.size < 32)
    (h : RD (deployedRuntime v) ee g s0 ⟨10060⟩
      (ptr :: w1 :: supplyIndex :: borrowIndex :: ⟨0⟩ :: R) mem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hsize : out.size < UInt256.size := by change out.size < 2^256; omega
  have r1 := cometWithExtendedAssetList_block_10060_taken
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [ugt_one (by rw [UInt256.toNat_ofNat_of_lt hsize]; exact hshort)]; decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_9693
    (immWords := wordsOf (immStore v)) (by change R.length + 10 + 2 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_9668
    (immWords := wordsOf (immStore v)) (by change R.length + 9 + 6 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  obtain ⟨aw4, k4, C4, r4⟩ := cometAllocateBounded (v := v) (bound := 1)
    (by change R.length + 11 + 6 ≤ 1024; omega)
    (by rw [UInt256.toNat_ofNat_of_lt hsize]; omega) hptr
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  have r5 := cometWithExtendedAssetList_block_9678
    (immWords := wordsOf (immStore v)) (by change R.length + 9 + 3 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
  have r6 := cometWithExtendedAssetList_block_9546_taken
    (immWords := wordsOf (immStore v)) (by change R.length + 9 + 4 ≤ 1024; omega)
    (by rw [word_add_sub_left, slt_ofNat_lit_one_low (by decide) hshort]; decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
  exact cometRevert1410 (by change R.length + 10 + 2 ≤ 1024; omega) r6

theorem cometReservesResponseFull {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr w1 supplyIndex borrowIndex : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024) (hlo : 96 ≤ ptr.toNat)
    (hptr : ptr.toNat + 36 < 2^64) (hout : 32 ≤ out.size) (hhi : out.size < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 ⟨10060⟩
      (ptr :: w1 :: supplyIndex :: borrowIndex :: ⟨0⟩ :: R)
      (tokenBalanceCopyMemory mem ptr ee.codeOwner out) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨9965⟩
      (⟨10048⟩ :: w1 :: supplyIndex :: borrowIndex :: calldataWord out 0 :: R)
      (tokenBalanceReturnMemory mem ptr ee.codeOwner out) aw' out σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_10060_fallthrough
    (immWords := wordsOf (immStore v)) (by omega)
    (ugt_zero (by rw [UInt256.toNat_ofNat_of_lt hhi]; exact hout)) h
  have r2 := cometWithExtendedAssetList_block_10094
    (immWords := wordsOf (immStore v)) (by change R.length + 9 + 6 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  obtain ⟨aw3, k3, C3, r3⟩ := cometAllocateBounded (v := v) (bound := 1)
    (by change R.length + 11 + 6 ≤ 1024; omega) (by decide) (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
  rw [show allocationEnd ptr (UInt256.ofNat 32) = ptr + ⟨32⟩ from rfl] at r3
  have r4 := cometWithExtendedAssetList_block_9678
    (immWords := wordsOf (immStore v)) (by change R.length + 9 + 3 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
  have r5 := cometWithExtendedAssetList_block_9546_fallthrough
    (immWords := wordsOf (immStore v)) (by change R.length + 9 + 4 ≤ 1024; omega)
    (by rw [word_add_sub_left]; decide) r4
  have r6 := cometWithExtendedAssetList_block_9558
    (immWords := wordsOf (immStore v)) (by change R.length + 8 + 2 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
  have r7 := cometWithExtendedAssetList_block_10103
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
  have hw := tokenBalanceReturnMemory_word (mem := mem) (owner := ee.codeOwner) hlo
    (by change ptr.toNat + 36 < 2^256; omega) hout hhi
  change RD _ _ _ _ _
    (⟨10048⟩ :: w1 :: supplyIndex :: borrowIndex ::
      memLoad ptr (tokenBalanceReturnMemory mem ptr ee.codeOwner out) :: R)
    (tokenBalanceReturnMemory mem ptr ee.codeOwner out) _ _ _ _ _ at r7
  rw [hw] at r7
  exact ⟨_, _, _, r7⟩

end Benchmarks.CompoundIII.Comet

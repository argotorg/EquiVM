import Benchmarks.CompoundIII.Comet.TokenBalanceMemory
import Benchmarks.CompoundIII.Comet.MemoryAllocate
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_037
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_045
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_046

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometTokenBalanceFailed {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr asset : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨9600⟩ (⟨0⟩ :: asset :: ptr :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_9600_taken
    (immWords := wordsOf (immStore v)) (by omega) (by decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_9700
    (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  exact cometWithExtendedAssetList_block_7166 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 4 ≤ 1024; omega)
    (by change 0 + out.size % UInt256.size ≤ out.size; simpa using Nat.mod_le out.size _) r2

theorem cometTokenBalanceResponseStart {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr asset : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨9600⟩ (⟨1⟩ :: asset :: ptr :: R)
      mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨9652⟩ (ptr :: asset :: ⟨0⟩ :: R)
      mem aw out σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_9600_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by decide) h
  have r2 := cometWithExtendedAssetList_block_9607_taken
    (immWords := wordsOf (immStore v)) hstack (by decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  exact ⟨_, _, r2⟩

theorem cometTokenBalanceShort {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr asset : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024) (hptr : ptr.toNat + 32 < 2^64)
    (hshort : out.size < 32)
    (h : RD (deployedRuntime v) ee g s0 ⟨9652⟩ (ptr :: asset :: ⟨0⟩ :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hsize : out.size < UInt256.size := by change out.size < 2^256; omega
  have r1 := cometWithExtendedAssetList_block_9652_taken
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [ugt_one (by rw [UInt256.toNat_ofNat_of_lt hsize]; exact hshort)]; decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_9693
    (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_9668
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 6 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  obtain ⟨aw4, k4, C4, r4⟩ := cometAllocateBounded (v := v) (bound := 1)
    (by change R.length + 4 + 6 ≤ 1024; omega)
    (by rw [UInt256.toNat_ofNat_of_lt hsize]; omega) hptr
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  have r5 := cometWithExtendedAssetList_block_9678
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 3 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
  have r6 := cometWithExtendedAssetList_block_9546_taken
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 4 ≤ 1024; omega)
    (by rw [word_add_sub_left, slt_ofNat_lit_one_low (by decide) hshort]; decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
  exact cometRevert1410 (by change R.length + 3 + 2 ≤ 1024; omega) r6

theorem cometTokenBalanceFull {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr asset : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024) (hlo : 96 ≤ ptr.toNat)
    (hptr : ptr.toNat + 36 < 2^64) (hout : 32 ≤ out.size) (hhi : out.size < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 ⟨9652⟩ (ptr :: asset :: ⟨0⟩ :: R)
      (tokenBalanceCopyMemory mem ptr ee.codeOwner out) aw out σ k C) :
    ∃ aw' k' C' dummy, RD (deployedRuntime v) ee g s0 ⟨9615⟩
      (dummy :: asset :: calldataWord out 0 :: R)
      (tokenBalanceReturnMemory mem ptr ee.codeOwner out) aw' out σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_9652_fallthrough
    (immWords := wordsOf (immStore v)) (by omega)
    (ugt_zero (by rw [UInt256.toNat_ofNat_of_lt hhi]; exact hout)) h
  have r2 := cometWithExtendedAssetList_block_9668
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 6 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  obtain ⟨aw3, k3, C3, r3⟩ := cometAllocateBounded (v := v) (bound := 1)
    (by change R.length + 4 + 6 ≤ 1024; omega) (by decide) (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
  rw [show allocationEnd ptr (UInt256.ofNat 32) = ptr + ⟨32⟩ from rfl] at r3
  have r4 := cometWithExtendedAssetList_block_9678
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 3 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
  have r5 := cometWithExtendedAssetList_block_9546_fallthrough
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 4 ≤ 1024; omega)
    (by rw [word_add_sub_left]; decide) r4
  have r6 := cometWithExtendedAssetList_block_9558
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 2 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
  have r7 := cometWithExtendedAssetList_block_9686
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
  have hw := tokenBalanceReturnMemory_word (mem := mem) (owner := ee.codeOwner) hlo
    (by change ptr.toNat + 36 < 2^256; omega) hout hhi
  change RD _ _ _ _ _
    (_ :: asset :: memLoad ptr (tokenBalanceReturnMemory mem ptr ee.codeOwner out) :: R)
    (tokenBalanceReturnMemory mem ptr ee.codeOwner out) _ _ _ _ _ at r7
  rw [hw] at r7
  exact ⟨_, _, _, _, r7⟩

end Benchmarks.CompoundIII.Comet

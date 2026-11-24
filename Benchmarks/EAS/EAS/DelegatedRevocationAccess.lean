import Benchmarks.EAS.EAS.DelegatedBatchIndex
import Benchmarks.EAS.EAS.FixedAllocate
import Benchmarks.EAS.EAS.RuntimeBlocks_006
import Benchmarks.EAS.EAS.RuntimeBlocks_007

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def delegatedRevocationReservedMemory (mem : ByteArray) (heap : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (heap.toNat+128))
def delegatedRevocationSchemaMemory (mem : ByteArray) (heap : UInt256) (schema : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord mem heap.toNat schema

theorem easDelegatedRevocationReserve {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {root heap a b c d : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+11 ≤ 1024) (hh : heap.toNat ≤ 2^64-1)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1318⟩ (root::a::b::c::d::R) mem aw rdata σ k C) :
    if delegatedBatchHeadValid ee.calldata root ∧ heap.toNat+128 ≤ 2^64-1 then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨1342⟩ (d::a::root::b::c::heap::R)
        (delegatedRevocationReservedMemory mem heap) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases hv : delegatedBatchHeadValid ee.calldata root
  · obtain ⟨a1,j1,D1,r1⟩ := easBlocks.eas_block_1318_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hv rd
    obtain ⟨a2,j2,D2,r2⟩ := easBlocks.eas_block_1330_packed (immWords := wordsOf (immStore v))
      (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [easBlocks.eas_block_1330_stack,easBlocks.eas_block_1318_fallthrough_stack,hfree] at r2
    have hn := fixedAllocation_next .bytes128 hh
    change allocateNext heap.toNat 128 = heap.toNat+128 at hn
    by_cases hg : heap.toNat+128 ≤ 2^64-1
    · rw [if_pos ⟨hv,hg⟩]
      obtain ⟨a3,j3,D3,r3⟩ := easFixedAllocate_ok v .bytes128 (by simp only [List.length_cons]; omega)
        (by change allocateNext heap.toNat 128 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 128; rw [hn]; exact ⟨hg,by omega⟩)
        (by rw [easPatchedValidJumps v]; jump_dest) r2
      exact ⟨a3,j3,D3,by simpa only [FixedAllocationSite.size,hn,delegatedRevocationReservedMemory] using r3⟩
    · rw [if_neg (fun h => hg h.2)]
      exact easFixedAllocate_revert v .bytes128 (by simp only [List.length_cons]; omega)
        (by change ¬(allocateNext heap.toNat 128 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 128); rw [hn]; exact fun h => hg h.1) r2
  · rw [if_neg (fun h => hv h.1)]
    obtain ⟨a1,j1,D1,r1⟩ := easBlocks.eas_block_1318_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hv (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_1318_taken_stack,List.length_cons]; omega) r1

theorem easDelegatedRevocationDataAccess {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {root row a b c d : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+13 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1342⟩ (d::a::root::b::c::row::R) mem aw rdata σ k C) :
    if delegatedBatchArrayAccess ee.calldata root 32 then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨5924⟩
        ((delegatedBatchArray ee.calldata root 32+UInt256.ofNat 32)::
          calldataWord ee.calldata (delegatedBatchArray ee.calldata root 32).toNat::UInt256.ofNat ee.calldata.size::
          ⟨1396⟩::d::a::root::b::c::row::R)
        (delegatedRevocationSchemaMemory mem row (calldataWord ee.calldata root.toNat)) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases ho : (calldataWord ee.calldata (root+UInt256.ofNat 32).toNat).toNat ≤ 2^64-1
  · obtain ⟨a1,j1,D1,r1⟩ := easBlocks.eas_block_1342_fallthrough_packed (immWords := wordsOf (immStore v))
      (by omega) (ugt_zero ho) rd
    by_cases hr : arrayHeaderReadable ee.calldata (delegatedBatchArray ee.calldata root 32)
    · rw [if_pos (show delegatedBatchArrayAccess ee.calldata root 32 from ⟨ho,hr⟩)]
      obtain ⟨a2,j2,D2,r2⟩ := easBlocks.eas_block_1367_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_1342_fallthrough_stack,List.length_cons]; omega) hr r1
      obtain ⟨a3,j3,D3,r3⟩ := easBlocks.eas_block_1380_packed (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_1367_fallthrough_stack,List.length_cons]; omega)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
      exact ⟨a3,j3,D3,r3⟩
    · rw [if_neg (fun h => hr h.2)]
      obtain ⟨a2,j2,D2,r2⟩ := easBlocks.eas_block_1367_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_1342_fallthrough_stack,List.length_cons]; omega) hr
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
      exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_1367_taken_stack,List.length_cons]; omega) r2
  · rw [if_neg (fun h => ho h.1)]
    obtain ⟨a1,j1,D1,r1⟩ := easBlocks.eas_block_1342_taken_packed (immWords := wordsOf (immStore v))
      (by omega) (by rw [ugt_one (by change 18446744073709551615 < (calldataWord ee.calldata (root+UInt256.ofNat 32).toNat).toNat; omega)]; decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_1342_taken_stack,List.length_cons]; omega) r1

end Benchmarks.EAS.EAS

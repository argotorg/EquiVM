import Benchmarks.EAS.EAS.DelegatedRevokeTailMemory
import Benchmarks.EAS.EAS.MemoryArrayIndex
import Benchmarks.EAS.EAS.RuntimeBlocks_006

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easDelegatedRevokeTailEVM {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap schema revoker : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+15 ≤ 1024)
    (hlo : 128 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hsize : ee.calldata.size < UInt256.size) (h100 : 100 ≤ ee.calldata.size) (hbig : ee.calldata.size < 2^255+4)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1136⟩ (revoker::schema::UInt256.ofNat 1180::R) mem aw rdata σ k C) :
    if heap.toNat+192 ≤ 2^64-1 then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨12085⟩
        (schema::heap::revoker::ee.weiValue::UInt256.ofNat 1180::R)
        (delegatedRevokeTailMemory mem heap ee.calldata) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_1136_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases h128 : heap.toNat+128 ≤ 2^64-1
  · obtain ⟨a2,k2,C2,r2⟩ := easOneRevocationAllocate v (by simp only [List.length_cons]; omega)
      (by omega) h128 hheap (by rw [easPatchedValidJumps v]; jump_dest) r1
    obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_1144_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
    have hn : (UInt256.ofNat (heap.toNat+128)).toNat = heap.toNat+128 := ulit_toNat' _ (by change _ < 2^256; omega)
    have hf := oneRevocationArrayMemory_views mem heap (by omega)
    have hr := easRevokeCalldataCopy (heap := UInt256.ofNat (heap.toNat+128)) v
      (by simp only [List.length_cons]; omega) hsize h100 hbig (by rw [hn]; exact h128) hf.2.2.1
      (by rw [easPatchedValidJumps v]; jump_dest) r3
    simp only [hn,show heap.toNat+128+64 = heap.toNat+192 by omega] at hr
    by_cases hg : heap.toNat+192 ≤ 2^64-1
    · rw [if_pos hg] at hr ⊢
      obtain ⟨a4,k4,C4,r4⟩ := hr
      obtain ⟨a5,k5,C5,r5⟩ := easBlocks.eas_block_1153_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r4
      have hc := delegatedRevokeCopiedMemory_facts mem heap ee.calldata hlo (by change _ < 2^256; omega)
      obtain ⟨a6,k6,C6,r6⟩ := easMemoryArrayFirst v
        (by simp only [easBlocks.eas_block_1153_stack,List.length_cons]; omega)
        (by change memLoad heap (delegatedRevokeCopiedMemory mem heap ee.calldata) ≠ ⟨0⟩; rw [hc.2.1]; decide)
        (by rw [easPatchedValidJumps v]; jump_dest) r5
      obtain ⟨a7,k7,C7,r7⟩ := easBlocks.eas_block_1162_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r6
      have ho : (UInt256.ofNat (heap.toNat+32)).toNat = heap.toNat+32 := ulit_toNat' _ (by change _ < 2^256; omega)
      simp only [easBlocks.eas_block_1162_memory,← writeWord_as_write,ho] at r7
      have hl : memLoad heap (delegatedRevokeTailMemory mem heap ee.calldata) = ⟨1⟩ :=
        (memLoad_write_below _ _ _ _ (le_refl _) (by have := hc.1; omega)).trans hc.2.1
      obtain ⟨a8,k8,C8,r8⟩ := easMemoryArrayFirst v
        (by simp only [easBlocks.eas_block_1162_stack,List.length_cons]; omega)
        (by change memLoad heap (delegatedRevokeTailMemory mem heap ee.calldata) ≠ ⟨0⟩; rw [hl]; decide)
        (by rw [easPatchedValidJumps v]; jump_dest) r7
      exact easBlocks.eas_block_1172_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r8
    · rw [if_neg hg] at hr ⊢
      exact hr
  · rw [if_neg (by omega : ¬ heap.toNat+192 ≤ 2^64-1)]
    exact easOneRevocationAllocate_revert v (by simp only [List.length_cons]; omega) (by omega) hh h128 hheap r1

end Benchmarks.EAS.EAS

import Benchmarks.EAS.EAS.FixedAllocate
import Benchmarks.EAS.EAS.WordSequence
import Benchmarks.EAS.EAS.RuntimeBlocks_027

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def defaultResultMemory (mem : ByteArray) (heap : UInt256) : ByteArray :=
  writeWordSequence (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat 64))) heap.toNat [⟨0⟩,⟨96⟩]

theorem easDefaultResultAllocate {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+7 ≤ 1024)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨7214⟩ (ret::R) mem aw rdata σ k C) :
    if allocateNext heap.toNat 64 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 64 then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (heap::R) (defaultResultMemory mem heap) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_7214_packed (immWords := wordsOf (immStore v)) (by omega)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_7214_stack,hheap] at r1
  by_cases hg : allocateNext heap.toNat 64 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 64
  · rw [if_pos hg]
    have hb : heap.toNat+32 < UInt256.size := by have hh := le_trans hg.2 hg.1; change heap.toNat+32 < 2^256; omega
    obtain ⟨a2,k2,C2,r2⟩ := easFixedAllocate_ok v .bytes64 (by simp only [List.length_cons]; omega) hg
      (by rw [easPatchedValidJumps v]; jump_dest) r1
    obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_7227_packed (immWords := wordsOf (immStore v)) (by omega) hret r2
    refine ⟨a3,k3,C3,?_⟩
    simpa only [easBlocks.eas_block_7227_stack,easBlocks.eas_block_7227_memory,
      defaultResultMemory,writeWordSequence,Reasoning.Theory.writeWord,uadd_word_ofNat_toNat heap 32 hb] using r3
  · rw [if_neg hg]
    exact easFixedAllocate_revert v .bytes64 (by simp only [List.length_cons]; omega) hg r1

theorem defaultResultMemory_heap (mem : ByteArray) (heap : UInt256) (hlo : 96 ≤ heap.toNat) :
    memLoad (UInt256.ofNat 64) (defaultResultMemory mem heap) = UInt256.ofNat (allocateNext heap.toNat 64) :=
  writeWordSequence_setFree_load64 mem heap.toNat _ _ hlo

theorem defaultResultMemory_prefix (mem : ByteArray) (heap : UInt256) :
    MemoryPrefix mem (defaultResultMemory mem heap) heap.toNat :=
  (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inr (by decide))).trans
    (writeWordSequence_prefix _ _ _ _ (le_refl _))

end Benchmarks.EAS.EAS

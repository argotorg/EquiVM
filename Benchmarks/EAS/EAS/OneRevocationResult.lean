import Benchmarks.EAS.EAS.OneRevocationAllocate
import Benchmarks.EAS.EAS.OneRequestMemory

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easOneRevocationAllocate_revert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+12 ≤ 1024)
    (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1) (hfail : ¬ heap.toNat+128 ≤ 2^64-1)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5745⟩ (ret::R) mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  have hn64 : allocateNext heap.toNat 64 = heap.toNat+64 := fixedAllocation_next .bytes64 hh
  have hn : (UInt256.ofNat (heap.toNat+64)).toNat = heap.toNat+64 := ulit_toNat' _ (by change _ < 2^256; omega)
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5745_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_5745_stack,hheap] at r1
  by_cases h64 : heap.toNat+64 ≤ 2^64-1
  · have hn128 : allocateNext (UInt256.ofNat (heap.toNat+64)).toNat 64 = heap.toNat+128 := by
      rw [hn]
      have hi := fixedAllocation_next .bytes64 h64
      change allocateNext (heap.toNat+64) 64 = heap.toNat+64+64 at hi
      exact hi.trans (by omega)
    obtain ⟨a2,k2,C2,r2⟩ := easAllocate_ok v (by simp only [List.length_cons]; omega)
      (by change allocateNext heap.toNat 64 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 64; rw [hn64]; exact ⟨h64,by omega⟩)
      (by rw [easPatchedValidJumps v]; jump_dest) r1
    obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_5762_packed (immWords := wordsOf (immStore v)) (by omega) r2
    change RD fork (deployedRuntime v) ee g s0 ⟨5805⟩ (⟨0⟩::heap::⟨32⟩::ret::heap::R)
      (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat 64))) heap.toNat ⟨1⟩)
      a3 rdata σ k3 C3 at r3
    rw [hn64] at r3
    change RD fork (deployedRuntime v) ee g s0 ⟨5805⟩ (⟨0⟩::heap::⟨32⟩::ret::heap::R)
      (oneRequestHeadMemory mem heap) a3 rdata σ k3 C3 at r3
    obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_5805_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r3
    obtain ⟨a5,k5,C5,r5⟩ := easBlocks.eas_block_5817_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r4
    have hf : memLoad (UInt256.ofNat 64) (oneRequestHeadMemory mem heap) = UInt256.ofNat (heap.toNat+64) := by
      exact writeWordSequence_setFree_load64 mem heap.toNat [⟨1⟩] _ hlo
    simp only [easBlocks.eas_block_5817_stack,hf] at r5
    exact easFixedAllocate_revert v .bytes64 (by simp only [List.length_cons]; omega)
      (by rw [FixedAllocationSite.size,hn128]; intro h; exact hfail h.1) r5
  · exact easAllocate_revert v (by simp only [List.length_cons]; omega)
      (by change ¬ (allocateNext heap.toNat 64 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 64)
          rw [hn64]; intro h; exact h64 h.1) r1

theorem oneRevocationArrayMemory_views (mem : ByteArray) (heap : UInt256) (hlo : 96 ≤ heap.toNat) :
    MemoryPrefix mem (oneRevocationArrayMemory mem heap) heap.toNat ∧
    heap.toNat+128 ≤ (oneRevocationArrayMemory mem heap).size ∧
    memLoad (UInt256.ofNat 64) (oneRevocationArrayMemory mem heap) = UInt256.ofNat (heap.toNat+128) ∧
    memLoad heap (oneRevocationArrayMemory mem heap) = ⟨1⟩ := by
  let m1 := oneRequestHeadMemory mem heap
  let m2 := Reasoning.Theory.writeWord m1 64 (UInt256.ofNat (heap.toNat+128))
  let m3 := writeWordSequence m2 (heap.toNat+64) [⟨0⟩,⟨0⟩]
  let final := Reasoning.Theory.writeWord m3 (heap.toNat+32) (UInt256.ofNat (heap.toNat+64))
  have hp1 : MemoryPrefix mem m1 heap.toNat :=
    (memoryPrefix_sparse_writeWord mem 64 heap.toNat _ (Or.inr (by decide))).trans
      (memoryPrefix_sparse_writeWord _ heap.toNat heap.toNat _ (Or.inl (le_refl _)))
  have hp2 : MemoryPrefix m1 m2 heap.toNat := memoryPrefix_sparse_writeWord _ 64 _ _ (Or.inr (by decide))
  have hp3 : MemoryPrefix m2 m3 (heap.toNat+64) := writeWordSequence_prefix _ _ _ _ (le_refl _)
  have hp4 : MemoryPrefix m3 final (heap.toNat+32) := memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (le_refl _))
  have hc1 : heap.toNat+32 ≤ m1.size := by change _ ≤ (Reasoning.Theory.writeWord _ heap.toNat _).size; rw [writeWord_sparse_size]; omega
  have hc2 : heap.toNat+32 ≤ m2.size := le_trans hc1 hp2.size
  have hc3 : heap.toNat+128 ≤ m3.size := writeWordSequence_covers m2 (heap.toNat+64) [⟨0⟩,⟨0⟩] (by simp)
  have hc4 := le_trans hc3 hp4.size
  have hf3 : memLoad (UInt256.ofNat 64) m3 = UInt256.ofNat (heap.toNat+128) :=
    writeWordSequence_setFree_load64 m1 _ _ _ (by omega)
  have hl1 : memLoad heap m1 = ⟨1⟩ := mloadWordValue_of_readWithPadding (by omega) (writeWord_sparse_read_back _ _ _)
  have hl2 : memLoad heap m2 = ⟨1⟩ := (memLoad_write_above m1 64 heap _ hlo hc1).trans hl1
  have hl3 : memLoad heap m3 = ⟨1⟩ := (memLoad_of_prefix hp3 heap hlo (by omega) hc2).trans hl2
  refine ⟨hp1.trans (hp2.trans ((hp3.mono (by omega)).trans (hp4.mono (by omega)))),hc4,?_,?_⟩
  · exact (memLoad_write_below m3 (heap.toNat+32) (UInt256.ofNat 64) _
      (by change 96 ≤ heap.toNat+32; omega) (by change 96 ≤ m3.size; omega)).trans hf3
  · exact (memLoad_of_prefix hp4 heap hlo (le_refl _) (by omega)).trans hl3

end Benchmarks.EAS.EAS

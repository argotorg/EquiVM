import Benchmarks.EAS.EAS.OneRequestAllocate
import Benchmarks.EAS.EAS.OneRequestMemory

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easOneRequestAllocate_revert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+12 ≤ 1024)
    (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1) (hfail : ¬ heap.toNat+256 ≤ 2^64-1)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨6864⟩ (ret::R) mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  have hn64 : allocateNext heap.toNat 64 = heap.toNat+64 := fixedAllocation_next .bytes64 hh
  have hn : (UInt256.ofNat (heap.toNat+64)).toNat = heap.toNat+64 := ulit_toNat' _ (by change _ < 2^256; omega)
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_6864_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_6864_stack,hheap] at r1
  by_cases h64 : heap.toNat+64 ≤ 2^64-1
  · have hn256 : allocateNext (UInt256.ofNat (heap.toNat+64)).toNat 192 = heap.toNat+256 := by
      rw [hn]
      have hi := fixedAllocation_next .bytes192 h64
      change allocateNext (heap.toNat+64) 192 = heap.toNat+64+192 at hi
      exact hi.trans (by omega)
    obtain ⟨a2,k2,C2,r2⟩ := easAllocate_ok v (by simp only [List.length_cons]; omega)
      (by change allocateNext heap.toNat 64 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 64; rw [hn64]; exact ⟨h64,by omega⟩)
      (by rw [easPatchedValidJumps v]; jump_dest) r1
    obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_6881_packed (immWords := wordsOf (immStore v)) (by omega) r2
    change RD fork (deployedRuntime v) ee g s0 ⟨6924⟩ (⟨0⟩::heap::⟨32⟩::ret::heap::R)
      (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat 64))) heap.toNat ⟨1⟩)
      a3 rdata σ k3 C3 at r3
    rw [hn64] at r3
    change RD fork (deployedRuntime v) ee g s0 ⟨6924⟩ (⟨0⟩::heap::⟨32⟩::ret::heap::R)
      (oneRequestHeadMemory mem heap) a3 rdata σ k3 C3 at r3
    obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_6924_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r3
    obtain ⟨a5,k5,C5,r5⟩ := easBlocks.eas_block_6936_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r4
    have hf : memLoad (UInt256.ofNat 64) (oneRequestHeadMemory mem heap) = UInt256.ofNat (heap.toNat+64) := by
      exact writeWordSequence_setFree_load64 mem heap.toNat [⟨1⟩] _ hlo
    simp only [easBlocks.eas_block_6936_stack,hf] at r5
    exact easFixedAllocate_revert v .bytes192 (by simp only [List.length_cons]; omega)
      (by rw [FixedAllocationSite.size,hn256]; intro h; exact hfail h.1) r5
  · exact easAllocate_revert v (by simp only [List.length_cons]; omega)
      (by change ¬ (allocateNext heap.toNat 64 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 64)
          rw [hn64]; intro h; exact h64 h.1) r1

end Benchmarks.EAS.EAS

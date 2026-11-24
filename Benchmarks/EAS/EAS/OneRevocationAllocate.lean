import Benchmarks.EAS.EAS.FixedAllocate
import Benchmarks.EAS.EAS.WordSequence
import Benchmarks.EAS.EAS.OneRequestAllocate
import Benchmarks.EAS.EAS.RuntimeBlocks_023

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def oneRevocationArrayMemory (mem : ByteArray) (heap : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord
    (writeWordSequence (Reasoning.Theory.writeWord (oneRequestHeadMemory mem heap) 64
      (UInt256.ofNat (heap.toNat+128))) (heap.toNat+64) [⟨0⟩,⟨0⟩])
    (heap.toNat+32) (UInt256.ofNat (heap.toNat+64))

theorem easOneRevocationAllocate {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+12 ≤ 1024)
    (hlo : 96 ≤ heap.toNat) (hh : heap.toNat+128 ≤ 2^64-1)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5745⟩ (ret::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (heap::R)
      (oneRevocationArrayMemory mem heap) aw' rdata σ k' C' := by
  have hh0 : heap.toNat ≤ 2^64-1 := by omega
  have hn64 : allocateNext heap.toNat 64 = heap.toNat+64 := fixedAllocation_next .bytes64 hh0
  have hn : (UInt256.ofNat (heap.toNat+64)).toNat = heap.toNat+64 := ulit_toNat' _ (by change _ < 2^256; omega)
  have hn128 : allocateNext (UInt256.ofNat (heap.toNat+64)).toNat 64 = heap.toNat+128 := by
    rw [hn]
    have hi := fixedAllocation_next .bytes64 (heap := heap.toNat+64) (by omega)
    change allocateNext (heap.toNat+64) 64 = heap.toNat+64+64 at hi
    exact hi.trans (by omega)
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5745_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_5745_stack,hheap] at r1
  obtain ⟨a2,k2,C2,r2⟩ := easAllocate_ok v (by simp only [List.length_cons]; omega)
    (by change allocateNext heap.toNat 64 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 64; rw [hn64]; constructor <;> omega)
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
  obtain ⟨a6,k6,C6,r6⟩ := easFixedAllocate_ok v .bytes64
    (by simp only [List.length_cons]; omega)
    (by change allocateNext (UInt256.ofNat (heap.toNat+64)).toNat 64 ≤ 2^64-1 ∧ (UInt256.ofNat (heap.toNat+64)).toNat ≤ allocateNext (UInt256.ofNat (heap.toNat+64)).toNat 64; rw [hn128,hn]; constructor <;> omega)
    (by rw [easPatchedValidJumps v]; jump_dest) r5
  simp only [FixedAllocationSite.size,hn128] at r6
  obtain ⟨a7,k7,C7,r7⟩ := easBlocks.eas_block_5832_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r6
  have hoff (n : Nat) (hn' : n ≤ 32) :
      (UInt256.ofNat (heap.toNat+64)+UInt256.ofNat n).toNat = heap.toNat+64+n := by
    rw [uadd_word_ofNat_toNat _ _ (by rw [hn]; change _ < 2^256; omega),hn]
  have hp : ((heap+⟨0⟩)+UInt256.ofNat 32).toNat = heap.toNat+32 := by
    rw [u256_add_zero]
    exact uadd_word_ofNat_toNat heap 32 (by change _ < 2^256; omega)
  have hm : easBlocks.eas_block_5832_memory
      (mem := Reasoning.Theory.writeWord (oneRequestHeadMemory mem heap) 64 (UInt256.ofNat (heap.toNat+128)))
      (x0 := UInt256.ofNat (heap.toNat+64)) (x1 := ⟨0⟩) (x2 := UInt256.ofNat 32) (x3 := heap) =
      oneRevocationArrayMemory mem heap := by
    simp only [easBlocks.eas_block_5832_memory,oneRevocationArrayMemory,writeWordSequence,Reasoning.Theory.writeWord]
    rw [hn,hp,hoff 32 (by decide)]
    simp only [Nat.add_assoc,Nat.reduceAdd,show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,show UInt256.ofNat 96 = (⟨96⟩ : UInt256) from rfl]
  rw [hm] at r7
  change RD fork (deployedRuntime v) ee g s0 ⟨5805⟩ (⟨32⟩::heap::⟨32⟩::ret::heap::R)
      (oneRevocationArrayMemory mem heap) a7 rdata σ k7 C7 at r7
  obtain ⟨a8,k8,C8,r8⟩ := easBlocks.eas_block_5805_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by decide) r7
  exact easBlocks.eas_block_5813_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hret r8

end Benchmarks.EAS.EAS

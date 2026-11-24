import Benchmarks.EAS.EAS.SignatureCalldata
import Benchmarks.EAS.EAS.FixedAllocate
import Benchmarks.EAS.EAS.RuntimeBlocks_025

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def signatureCopyMemory (mem : ByteArray) (heap : UInt256) (s : SignatureRecord) : ByteArray :=
  writeWordSequence (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (heap.toNat+96))) heap.toNat [s.v,s.r,s.s]

theorem signatureCopyMemory_facts (mem : ByteArray) (heap : UInt256) (s : SignatureRecord)
    (hlo : 96 ≤ heap.toNat) (hb : heap.toNat+96 < UInt256.size) (hc : signatureClean s) :
    MemoryPrefix mem (signatureCopyMemory mem heap s) heap.toNat ∧
    SignatureMemoryView (signatureCopyMemory mem heap s) heap s ∧
    memLoad (UInt256.ofNat 64) (signatureCopyMemory mem heap s) = UInt256.ofNat (heap.toNat+96) := by
  have hcover : heap.toNat+96 ≤ (signatureCopyMemory mem heap s).size :=
    writeWordSequence_covers _ heap.toNat [s.v,s.r,s.s] (by simp)
  have hget (i : Nat) (hi : i < 3) :
      memLoad (UInt256.ofNat (heap.toNat+32*i)) (signatureCopyMemory mem heap s) = [s.v,s.r,s.s][i] :=
    writeWordSequence_load_index _ _ _ _ hi (by omega)
  have hptr (n : Nat) (hn : n ≤ 96) : heap+UInt256.ofNat n = UInt256.ofNat (heap.toNat+n) := by
    apply u256_inj
    rw [uadd_word_ofNat_toNat heap n (by omega),ulit_toNat' _ (by omega)]
  refine ⟨?_,⟨hlo,hcover,?_,?_,?_⟩,writeWordSequence_setFree_load64 _ _ _ _ hlo⟩
  · exact (memoryPrefix_sparse_writeWord mem 64 heap.toNat _ (Or.inr (by decide))).trans
      (writeWordSequence_prefix _ heap.toNat heap.toNat _ (le_refl _))
  · have hg := hget 0 (by decide)
    simp only [Nat.mul_zero,Nat.add_zero,u256_ofNat_toNat,List.getElem_cons_zero] at hg
    rw [hg]
    exact hc.symm
  · rw [hptr 32 (by decide)]
    exact hget 1 (by decide)
  · rw [hptr 64 (by decide)]
    exact hget 2 (by decide)

theorem easSignatureCalldataCopy {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr heap ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+9 ≤ 1024)
    (hh : heap.toNat ≤ 2^64-1) (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨6273⟩ (ptr::UInt256.ofNat ee.calldata.size::ret::R) mem aw rdata σ k C) :
    ((signatureAtValid ee.calldata ptr ∧ heap.toNat+96 ≤ 2^64-1) →
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (heap::R)
        (signatureCopyMemory mem heap (signatureAt ee.calldata ptr)) aw' rdata σ k' C') ∧
    (¬ (signatureAtValid ee.calldata ptr ∧ heap.toNat+96 ≤ 2^64-1) → RDrev fork (deployedRuntime v) g s0) := by
  by_cases hhead : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ptr) ⟨96⟩ = ⟨0⟩
  · obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_6273_fallthrough_packed (immWords := wordsOf (immStore v))
      (by omega) hhead rd
    obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_6286_packed (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_6273_fallthrough_stack,List.length_cons]; omega)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [easBlocks.eas_block_6286_stack,easBlocks.eas_block_6273_fallthrough_stack,hheap] at r2
    have hn : allocateNext heap.toNat 96 = heap.toNat+96 := fixedAllocation_next .bytes96 hh
    by_cases hg : heap.toNat+96 ≤ 2^64-1
    · obtain ⟨a3,k3,C3,r3⟩ := easFixedAllocate_ok v .bytes96 (by simp only [List.length_cons]; omega)
        (by rw [FixedAllocationSite.size,hn]; exact ⟨hg,by omega⟩)
        (by rw [easPatchedValidJumps v]; jump_dest) r2
      simp only [FixedAllocationSite.size,hn] at r3
      by_cases hc : signatureClean (signatureAt ee.calldata ptr)
      · have he : UInt256.sub (calldataWord ee.calldata ptr.toNat)
            (UInt256.land (calldataWord ee.calldata ptr.toNat) (UInt256.ofNat 255)) = ⟨0⟩ := by
          change calldataWord ee.calldata ptr.toNat = UInt256.land (calldataWord ee.calldata ptr.toNat) (UInt256.ofNat 255) at hc
          rw [← hc,u256_sub_self]
        obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_6297_fallthrough_packed (immWords := wordsOf (immStore v))
          (by omega) he r3
        obtain ⟨a5,k5,C5,r5⟩ := easBlocks.eas_block_6312_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) hret r4
        have hm : easBlocks.eas_block_6312_memory (ee := ee)
            (mem := Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (heap.toNat+96)))
            (x0 := calldataWord ee.calldata ptr.toNat) (x1 := ptr) (x2 := heap) =
            signatureCopyMemory mem heap (signatureAt ee.calldata ptr) := by
          simp only [easBlocks.eas_block_6312_memory,← writeWord_as_write,signatureCopyMemory,signatureAt,writeWordSequence,
            uadd_word_ofNat_toNat heap 32 (by change heap.toNat+32 < 2^256; omega),
            uadd_word_ofNat_toNat heap 64 (by change heap.toNat+64 < 2^256; omega)]
        rw [hm] at r5
        exact ⟨fun _ => ⟨a5,k5,C5,r5⟩,fun h => False.elim (h ⟨⟨hhead,hc⟩,hg⟩)⟩
      · obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_6297_taken_packed (immWords := wordsOf (immStore v))
          (by omega) (u256_sub_ne_zero_of_ne hc) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r3
        have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
          (by simp only [easBlocks.eas_block_6297_taken_stack,List.length_cons]; omega) r4
        exact ⟨fun h => False.elim (hc h.1.2),fun _ => hr⟩
    · have hr := easFixedAllocate_revert v .bytes96 (by simp only [List.length_cons]; omega)
        (by rw [FixedAllocationSite.size,hn]; intro h; exact hg h.1) r2
      exact ⟨fun h => False.elim (hg h.2),fun _ => hr⟩
  · obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_6273_taken_packed (immWords := wordsOf (immStore v))
      (by omega) hhead (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_6273_taken_stack,List.length_cons]; omega) r1
    exact ⟨fun h => False.elim (hhead h.1.1),fun _ => hr⟩

end Benchmarks.EAS.EAS

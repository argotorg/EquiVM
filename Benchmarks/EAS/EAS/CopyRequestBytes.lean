import Benchmarks.EAS.EAS.CopyRequestFields
import Benchmarks.EAS.EAS.BytesAllocationEVM
import Benchmarks.EAS.EAS.RuntimeBlocks_022

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def requestCopyBytesValid (cd : ByteArray) (src off stop heap : UInt256) : Prop :=
  let tail := src+off
  let len := calldataWord cd tail.toNat
  UInt256.isZero (UInt256.slt (tail+⟨31⟩) stop) = ⟨0⟩ ∧
  len.toNat ≤ 2^64-1 ∧
  (allocateNext heap.toNat (bytesAllocation len.toNat) ≤ 2^64-1 ∧
    heap.toNat ≤ allocateNext heap.toNat (bytesAllocation len.toNat)) ∧
  UInt256.gt ((tail+len)+⟨32⟩) stop = ⟨0⟩
instance (cd : ByteArray) (src off stop heap : UInt256) : Decidable (requestCopyBytesValid cd src off stop heap) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def requestCopyPayloadMemory (mem cd : ByteArray) (src tail heap record len : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord
    (Reasoning.Theory.writeWord
      (Reasoning.Theory.writeWord
        (cd.write (tail+⟨32⟩).toNat mem (heap+⟨32⟩).toNat len.toNat)
        ((heap+len)+⟨32⟩).toNat ⟨0⟩)
      (record+⟨128⟩).toNat heap)
    (record+⟨160⟩).toNat (requestCopyWord cd src 160)

def requestCopyBytesMemory (mem cd : ByteArray) (src off heap record : UInt256) : ByteArray :=
  let len := calldataWord cd (src+off).toNat
  requestCopyPayloadMemory
    (Reasoning.Theory.writeWord
      (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat (bytesAllocation len.toNat))))
      heap.toNat len)
    cd src (src+off) heap record len

set_option maxHeartbeats 500000 in
theorem easCopyRequestBytes {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src off stop heap record ret : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+13 ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5459⟩ (off::src::stop::record::ret::R) mem aw rdata σ k C) :
    if requestCopyBytesValid ee.calldata src off stop heap then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret R
        (requestCopyBytesMemory mem ee.calldata src off heap record) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  let tail := src+off
  let len := calldataWord ee.calldata tail.toNat
  by_cases hh : UInt256.isZero (UInt256.slt (tail+⟨31⟩) stop) = ⟨0⟩
  · obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5459_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hh rd
    obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_5473_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
    have hl := easBytesAllocation v (by simp only [List.length_cons]; omega)
      (by rw [easPatchedValidJumps v]; jump_dest) r2
    by_cases hn : len.toNat ≤ 2^64-1
    · rw [if_pos hn] at hl
      obtain ⟨a3,k3,C3,r3⟩ := hl
      obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_5484_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r3
      simp only [easBlocks.eas_block_5484_stack,hfree] at r4
      change RD fork (deployedRuntime v) ee g s0 ⟨4883⟩
        (heap::UInt256.ofNat (bytesAllocation len.toNat)::⟨5498⟩::stop::heap::src::tail::len::record::ret::R)
        mem a4 rdata σ k4 C4 at r4
      have hsz : (UInt256.ofNat (bytesAllocation len.toNat)).toNat = bytesAllocation len.toNat := by
        apply ulit_toNat'
        change 32+(len.toNat+31)/32*32 < 2^256
        omega
      by_cases hg : allocateNext heap.toNat (bytesAllocation len.toNat) ≤ 2^64-1 ∧
          heap.toNat ≤ allocateNext heap.toNat (bytesAllocation len.toNat)
      · obtain ⟨a5,k5,C5,r5⟩ := easAllocate_ok v (by simp only [List.length_cons]; omega)
          (by simpa only [hsz] using hg) (by rw [easPatchedValidJumps v]; jump_dest) r4
        by_cases he : UInt256.gt ((tail+len)+⟨32⟩) stop = ⟨0⟩
        · rw [if_pos ⟨hh,hn,hg,he⟩]
          obtain ⟨a6,k6,C6,r6⟩ := easBlocks.eas_block_5498_fallthrough_packed (immWords := wordsOf (immStore v))
            (by simp only [List.length_cons]; omega) he r5
          obtain ⟨a7,k7,C7,r7⟩ := easBlocks.eas_block_5513_packed (immWords := wordsOf (immStore v)) hstack hret r6
          refine ⟨a7,k7,C7,?_⟩
          simpa only [easBlocks.eas_block_5513_stack,easBlocks.eas_block_5513_memory,
            easBlocks.eas_block_5498_fallthrough_memory,requestCopyBytesMemory,requestCopyPayloadMemory,
            requestCopyWord,Reasoning.Theory.writeWord,hsz] using r7
        · rw [if_neg (fun h => he h.2.2.2)]
          obtain ⟨a6,k6,C6,r6⟩ := easBlocks.eas_block_5498_taken_packed (immWords := wordsOf (immStore v))
            (by simp only [List.length_cons]; omega) he (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r5
          exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
            (by simp only [easBlocks.eas_block_5498_taken_stack,List.length_cons]; omega) r6
      · rw [if_neg (fun h => hg h.2.2.1)]
        exact easAllocate_revert v (by simp only [List.length_cons]; omega) (by simpa only [hsz] using hg) r4
    · rw [if_neg (fun h => hn h.2.1)]
      rw [if_neg hn] at hl
      exact hl
  · rw [if_neg (fun h => hh h.1)]
    obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5459_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hh (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_5459_taken_stack,List.length_cons]; omega) r1

end Benchmarks.EAS.EAS

import Benchmarks.EAS.EAS.RefundResult
import Benchmarks.EAS.EAS.BytesAllocationEVM
import Benchmarks.EAS.EAS.ReturnDataMemory
import Benchmarks.EAS.EAS.RuntimeBlocks_053

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def refundMemory (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  if out.size = 0 then mem else bytesReturnMemory mem ptr (allocateNext ptr.toNat (bytesAllocation out.size)) out

theorem refundMemory_prefix (mem : ByteArray) (ptr : UInt256) (out : ByteArray) :
    MemoryPrefix mem (refundMemory mem ptr out) ptr.toNat := by
  unfold refundMemory
  split
  · exact MemoryPrefix.refl _ _
  · exact bytesReturnMemory_prefix _ _ _ _

theorem refundMemory_heap {mem : ByteArray} {ptr : UInt256} (out : ByteArray)
    (hlo : 96 ≤ ptr.toNat) (hh : memLoad (UInt256.ofNat 64) mem = ptr) :
    memLoad (UInt256.ofNat 64) (refundMemory mem ptr out) = UInt256.ofNat (refundNext ptr.toNat out.size) := by
  unfold refundMemory refundNext
  split
  · simpa only [u256_ofNat_toNat] using hh
  · exact bytesReturnMemory_heap _ _ _ _ hlo

theorem refundAllocationEVM {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr flag ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+12 ≤ 1024) (hout : out.size < UInt256.size) (hheap : ptr.toNat ≤ 2^64-1)
    (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16367⟩ (flag::ret::R) mem aw out σ k C) :
    if refundAllocationValid ptr.toNat out.size then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨16407⟩ (flag::ret::R) (refundMemory mem ptr out) aw' out σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have hlen : (UInt256.ofNat out.size).toNat = out.size := ulit_toNat' _ hout
  by_cases hz : out.size = 0
  · have hv : refundAllocationValid ptr.toNat out.size := Or.inl hz
    rw [if_pos hv, refundMemory, if_pos hz]
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16367_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [hz]; decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_16546_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
  · obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16367_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne (fun h => hz (by
        have ht := congrArg UInt256.toNat h
        simpa only [hlen] using ht))) rd
    obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_16373_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    have ha := easBytesAllocation v (by simp only [List.length_cons]; omega)
      (by rw [easPatchedValidJumps v]; jump_dest) rd2
    simp only [hlen] at ha
    by_cases hl : out.size ≤ 2^64-1
    · rw [if_pos hl] at ha
      obtain ⟨aw3,k3,C3,rd3⟩ := ha
      obtain ⟨aw4,k4,C4,rd4⟩ := easBlocks.eas_block_16382_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd3
      simp only [easBlocks.eas_block_16382_stack, hh] at rd4
      have hs : (UInt256.ofNat (bytesAllocation out.size)).toNat = bytesAllocation out.size :=
        ulit_toNat' _ (by unfold bytesAllocation; change 32+(out.size+31)/32*32 < 2^256; omega)
      by_cases hg : allocateNext ptr.toNat (bytesAllocation out.size) ≤ 2^64-1 ∧
          ptr.toNat ≤ allocateNext ptr.toNat (bytesAllocation out.size)
      · have hv : refundAllocationValid ptr.toNat out.size := Or.inr ⟨hl,hg⟩
        rw [if_pos hv, refundMemory, if_neg hz]
        obtain ⟨aw5,k5,C5,rd5⟩ := easAllocate_ok v (by simp only [List.length_cons]; omega)
          (by simpa only [hs] using hg) (by rw [easPatchedValidJumps v]; jump_dest) rd4
        simp only [hs] at rd5
        obtain ⟨aw6,k6,C6,rd6⟩ := easBlocks.eas_block_16396_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [hlen]; change 0+out.size ≤ out.size; omega) rd5
        refine ⟨aw6,k6,C6,?_⟩
        have hp : (ptr+UInt256.ofNat 32).toNat = ptr.toNat+32 :=
          uadd_word_ofNat_toNat ptr 32 (by change ptr.toNat+32 < 2^256; omega)
        simpa only [easBlocks.eas_block_16396_stack, easBlocks.eas_block_16396_memory,
          bytesReturnMemory, hlen, hp] using rd6
      · have hv : ¬ refundAllocationValid ptr.toNat out.size := fun h => hg ((h.resolve_left hz).2)
        rw [if_neg hv]
        exact easAllocate_revert v (by simp only [List.length_cons]; omega) (by simpa only [hs] using hg) rd4
    · have hv : ¬ refundAllocationValid ptr.toNat out.size := fun h => hl ((h.resolve_left hz).1)
      rw [if_neg hv]
      simpa only [if_neg hl] using ha

theorem refundFinish {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {ret : UInt256} {R : List UInt256} (v : EASImmutables) (success : Bool)
    (hstack : R.length+6 ≤ 1024) (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16407⟩ ((if success then ⟨1⟩ else ⟨0⟩)::ret::R) mem aw out σ k C) :
    if success then ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret R mem aw' out σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  cases success with
  | true =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16407_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by decide) rd
    exact easBlocks.eas_block_16413_packed (immWords := wordsOf (immStore v)) (by omega) hvalid rd1
  | false =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16407_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by decide) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_16414 (immWords := wordsOf (immStore v)) (by simp only [easBlocks.eas_block_16407_taken_stack, List.length_cons]; omega) rd1

theorem refundReturnEVM {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256} (v : EASImmutables) (success : Bool)
    (hstack : R.length+12 ≤ 1024) (hout : out.size < UInt256.size) (hheap : ptr.toNat ≤ 2^64-1)
    (hh : memLoad (UInt256.ofNat 64) mem = ptr) (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16367⟩ ((if success then ⟨1⟩ else ⟨0⟩)::ret::R) mem aw out σ k C) :
    if refundResultValid ptr.toNat success out then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret R (refundMemory mem ptr out) aw' out σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have ha := refundAllocationEVM v hstack hout hheap hh rd
  by_cases hg : refundAllocationValid ptr.toNat out.size
  · rw [if_pos hg] at ha
    obtain ⟨aw1,k1,C1,rd1⟩ := ha
    have hf := refundFinish v success (by omega) hvalid rd1
    cases success <;> simpa only [refundResultValid, hg, Bool.false_eq_true, false_and, true_and, if_false, if_true] using hf
  · have hv : ¬ refundResultValid ptr.toNat success out := fun h => hg h.2
    rw [if_neg hv]
    simpa only [if_neg hg] using ha

end Benchmarks.EAS.EAS

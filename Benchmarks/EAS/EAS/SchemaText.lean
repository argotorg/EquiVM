import Benchmarks.EAS.EAS.SchemaHead
import Benchmarks.EAS.EAS.BytesAllocationEVM
import Benchmarks.EAS.EAS.CopyPreserve

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

def schemaTextMemory (mem : ByteArray) (text heap record len : UInt256) : ByteArray :=
  let next := allocateNext heap.toNat (bytesAllocation len.toNat)
  let m1 := Reasoning.Theory.writeWord mem 64 (UInt256.ofNat next)
  let m2 := Reasoning.Theory.writeWord m1 heap.toNat len
  let m3 := Reasoning.Theory.writeWord
    (easCopyWords (text+UInt256.ofNat 32) (heap+UInt256.ofNat 32) m2 0 ((len.toNat+31)/32))
    (len+(heap+UInt256.ofNat 32)).toNat ⟨0⟩
  Reasoning.Theory.writeWord m3 (record+UInt256.ofNat 96).toNat heap

theorem easSchemaText {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {text heap record len ending ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+12 ≤ 1024) (htext : text.toNat < 2^140) (hheap : heap.toNat ≤ 2^64-1)
    (hl : memLoad text mem = len) (hh : memLoad (UInt256.ofNat 64) mem = heap)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨7479⟩ (text::ending::record::ret::R) mem aw out σ k C) :
    if len.toNat ≤ 2^64-1 ∧
        (allocateNext heap.toNat (bytesAllocation len.toNat) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (bytesAllocation len.toNat)) ∧
        text.toNat+len.toNat+32 ≤ ending.toNat then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (record::R)
        (schemaTextMemory mem text heap record len) aw' out σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_7479_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_7479_stack,hl] at rd1
  have hr := easBytesAllocation v (by simp only [List.length_cons]; omega)
    (by rw [easPatchedValidJumps v]; jump_dest) rd1
  by_cases hlen : len.toNat ≤ 2^64-1
  · rw [if_pos hlen] at hr
    obtain ⟨aw2,k2,C2,rd2⟩ := hr
    obtain ⟨aw3,k3,C3,rd3⟩ := easBlocks.eas_block_7489_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
    simp only [easBlocks.eas_block_7489_stack,hh] at rd3
    have hsize : (UInt256.ofNat (bytesAllocation len.toNat)).toNat = bytesAllocation len.toNat :=
      ulit_toNat' _ (by unfold bytesAllocation; change 32+(len.toNat+31)/32*32 < 2^256; omega)
    have hend : ((text+len)+UInt256.ofNat 32).toNat = text.toNat+len.toNat+32 := by
      have ht : (text+len).toNat = text.toNat+len.toNat := by
        rw [uadd_toNat,Nat.mod_eq_of_lt (by change text.toNat+len.toNat < 2^256; omega)]
      rw [uadd_word_ofNat_toNat _ 32 (by rw [ht]; change _ < 2^256; omega),ht]
    by_cases hg : allocateNext heap.toNat (bytesAllocation len.toNat) ≤ 2^64-1 ∧
        heap.toNat ≤ allocateNext heap.toNat (bytesAllocation len.toNat)
    · obtain ⟨aw4,k4,C4,rd4⟩ := easAllocate_ok v (by simp only [List.length_cons]; omega)
        (by simpa only [hsize] using hg) (by rw [easPatchedValidJumps v]; jump_dest) rd3
      by_cases hext : text.toNat+len.toNat+32 ≤ ending.toNat
      · rw [if_pos ⟨hlen,hg,hext⟩]
        obtain ⟨aw5,k5,C5,rd5⟩ := easBlocks.eas_block_7503_fallthrough_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (ugt_zero (by rw [hend]; exact hext)) rd4
        obtain ⟨aw6,k6,C6,rd6⟩ := easBlocks.eas_block_7518_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd5
        obtain ⟨aw7,k7,C7,rd7⟩ := easCopy v (by simp only [List.length_cons]; omega)
          (by change len.toNat+31 < 2^256; omega) (by rw [easPatchedValidJumps v]; jump_dest) rd6
        obtain ⟨aw8,k8,C8,rd8⟩ := easBlocks.eas_block_7533_packed (immWords := wordsOf (immStore v))
          (by omega) hvalid rd7
        refine ⟨aw8,k8,C8,?_⟩
        simpa only [easBlocks.eas_block_7533_stack,easBlocks.eas_block_7533_memory,
          easBlocks.eas_block_7503_fallthrough_memory,hsize,schemaTextMemory,Reasoning.Theory.writeWord] using rd8
      · rw [if_neg (by intro h; exact hext h.2.2)]
        obtain ⟨aw5,k5,C5,rd5⟩ := easBlocks.eas_block_7503_taken_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [ugt_one (by rw [hend]; omega)]; decide)
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd4
        exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
          (by simp only [easBlocks.eas_block_7503_taken_stack,List.length_cons]; omega) rd5
    · rw [if_neg (by intro h; exact hg h.2.1)]
      exact easAllocate_revert v (by simp only [List.length_cons]; omega) (by simpa only [hsize] using hg) rd3
  · rw [if_neg hlen] at hr
    rw [if_neg (by intro h; exact hlen h.1)]
    exact hr

end Benchmarks.EAS.EAS

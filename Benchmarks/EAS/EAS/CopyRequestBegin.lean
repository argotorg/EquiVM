import Benchmarks.EAS.EAS.CopyRequestFields
import Benchmarks.EAS.EAS.FixedAllocate

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easCopyRequestBegin {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src heap stop ret : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+9 ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5344⟩ (src::stop::ret::R) mem aw rdata σ k C) :
    if UInt256.slt (UInt256.sub stop src) ⟨192⟩ = ⟨0⟩ then
      if allocateNext heap.toNat 192 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 192 then
        ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨5369⟩ (stop::heap::ret::src::R)
          (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat 192))) aw' rdata σ k' C'
      else RDrev fork (deployedRuntime v) g s0
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases hh : UInt256.slt (UInt256.sub stop src) ⟨192⟩ = ⟨0⟩
  · rw [if_pos hh]
    obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5344_fallthrough_packed (immWords := wordsOf (immStore v))
      (by omega) hh rd
    obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_5357_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [easBlocks.eas_block_5357_stack,hfree] at r2
    by_cases hg : allocateNext heap.toNat 192 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 192
    · rw [if_pos hg]
      exact easFixedAllocate_ok v .bytes192 (by simp only [List.length_cons]; omega) hg
        (by rw [easPatchedValidJumps v]; jump_dest) r2
    · rw [if_neg hg]
      exact easFixedAllocate_revert v .bytes192 (by simp only [List.length_cons]; omega) hg r2
  · rw [if_neg hh]
    obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5344_taken_packed (immWords := wordsOf (immStore v))
      (by omega) hh (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_5344_taken_stack,List.length_cons]; omega) r1

end Benchmarks.EAS.EAS

import Benchmarks.EAS.EAS.ArrayAllocationHead
import Benchmarks.EAS.EAS.RuntimeBlocks_022

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def requestArrayHeadValid (offset len stop heap : UInt256) : Prop :=
  len.toNat ≤ 2^64-1 ∧
  (allocateNext heap.toNat (32+32*len.toNat) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (32+32*len.toNat)) ∧
  UInt256.gt (offset+UInt256.shiftLeft len (UInt256.ofNat 5)) stop = ⟨0⟩
instance (offset len stop heap : UInt256) : Decidable (requestArrayHeadValid offset len stop heap) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem easCopyRequestArrayHead {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {offset len stop heap ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+12 ≤ 1024)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5544⟩ (offset::len::stop::ret::R) mem aw rdata σ k C) :
    (requestArrayHeadValid offset len stop heap →
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨5594⟩
        ((heap+UInt256.ofNat 32)::offset::offset::(offset+UInt256.shiftLeft len (UInt256.ofNat 5))::stop::ret::heap::R)
        (arrayAllocationHeaderMemory mem heap len.toNat) aw' rdata σ k' C') ∧
    (¬ requestArrayHeadValid offset len stop heap → RDrev fork (deployedRuntime v) g s0) := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5544_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_5544_stack] at r1
  have hsize := easArrayAllocationSize v (by simp only [List.length_cons]; omega)
    (by rw [easPatchedValidJumps v]; jump_dest) r1
  by_cases hl : len.toNat ≤ 2^64-1
  · rw [if_pos hl] at hsize
    obtain ⟨a2,k2,C2,r2⟩ := hsize
    obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_5556_packed (immWords := wordsOf (immStore v))
      (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
    simp only [easBlocks.eas_block_5556_stack,hheap] at r3
    have hn : (UInt256.ofNat (32+32*len.toNat)).toNat = 32+32*len.toNat :=
      ulit_toNat' _ (by change _ < 2^256; omega)
    by_cases hg : allocateNext heap.toNat (32+32*len.toNat) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (32+32*len.toNat)
    · obtain ⟨a4,k4,C4,r4⟩ := easAllocate_ok v (by simp only [List.length_cons]; omega)
        (by simpa only [hn] using hg) (by rw [easPatchedValidJumps v]; jump_dest) r3
      rw [hn] at r4
      constructor
      · intro hv
        obtain ⟨a5,k5,C5,r5⟩ := easBlocks.eas_block_5570_fallthrough_packed (immWords := wordsOf (immStore v))
          (by omega) hv.2.2 r4
        obtain ⟨a6,k6,C6,r6⟩ := easBlocks.eas_block_5592_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) r5
        refine ⟨a6,k6,C6,?_⟩
        simpa only [easBlocks.eas_block_5592_stack,easBlocks.eas_block_5570_fallthrough_stack,
          easBlocks.eas_block_5570_fallthrough_memory,arrayAllocationHeaderMemory,Reasoning.Theory.writeWord,u256_ofNat_toNat] using r6
      · intro hv
        have he : UInt256.gt (offset+UInt256.shiftLeft len (UInt256.ofNat 5)) stop ≠ ⟨0⟩ := fun he => hv ⟨hl,hg,he⟩
        obtain ⟨a5,k5,C5,r5⟩ := easBlocks.eas_block_5570_taken_packed (immWords := wordsOf (immStore v))
          (by omega) he (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r4
        exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
          (by simp only [easBlocks.eas_block_5570_taken_stack,List.length_cons]; omega) r5
    · exact ⟨fun h => False.elim (hg h.2.1),fun _ =>
        easAllocate_revert v (by simp only [List.length_cons]; omega) (by simpa only [hn] using hg) r3⟩
  · rw [if_neg hl] at hsize
    exact ⟨fun h => False.elim (hl h.1),fun _ => hsize⟩

end Benchmarks.EAS.EAS

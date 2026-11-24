import Benchmarks.EAS.EAS.WordArrayAllocationView
import Benchmarks.EAS.EAS.WordArrayPrefix
import Benchmarks.EAS.EAS.RuntimeBlocks_037

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easMergeUIDAllocate {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {lists len heap ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+12 ≤ 1024) (hh : heap.toNat ≤ 2^64-1)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap) (hcd : ee.calldata.size < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨11975⟩ (lists::len::ret::R) mem aw rdata σ k C) :
    (len.toNat ≤ 2^64-1 ∧ (allocateNext heap.toNat (32+32*len.toNat) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (32+32*len.toNat)) →
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨11990⟩ (heap::⟨0⟩::⟨0⟩::lists::ret::R)
        (wordArrayAllocationMemory mem ee.calldata heap len.toNat) aw' rdata σ k' C') ∧
    (¬ (len.toNat ≤ 2^64-1 ∧ (allocateNext heap.toNat (32+32*len.toNat) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (32+32*len.toNat))) →
      RDrev fork (deployedRuntime v) g s0) := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_11975_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  have hr := easWordArrayAllocate v (by simp only [List.length_cons]; omega) hh hfree hcd
    (by rw [easPatchedValidJumps v]; jump_dest) r1
  constructor
  · intro hv
    rw [if_pos hv.1,if_pos hv.2] at hr
    obtain ⟨a2,k2,C2,r2⟩ := hr
    exact easBlocks.eas_block_11985_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) r2
  · intro hv
    by_cases hl : len.toNat ≤ 2^64-1
    · rw [if_pos hl,if_neg (fun h => hv ⟨hl,h⟩)] at hr
      exact hr
    · rw [if_neg hl] at hr
      exact hr

theorem mergeUIDAllocateMemory (mem calldata : ByteArray) (heap : UInt256) (n : Nat)
    (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1) (hn : n ≤ 2^64-1) :
    let next := allocateNext heap.toNat (32+32*n)
    let final := wordArrayAllocationMemory mem calldata heap n
    MemoryPrefix mem final heap.toNat ∧ WordArrayPrefixView final heap (List.replicate n ⟨0⟩) 0 next ∧
    memLoad (UInt256.ofNat 64) final = UInt256.ofNat next := by
  dsimp only
  have hm := wordArrayAllocationMemory_view mem calldata heap n hlo hh hn
  refine ⟨hm.1,⟨hlo,by simp only [List.length_replicate]; omega,?_,?_,?_,?_⟩,hm.2.2.2.1⟩
  · rw [List.length_replicate,allocateNext_wordArray hh hn]
  · simp only [Nat.mul_zero,Nat.add_zero]
    exact hm.2.1
  · simpa only [List.length_replicate] using hm.2.2.1
  · intro i hi
    omega

end Benchmarks.EAS.EAS

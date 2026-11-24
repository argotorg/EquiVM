import Benchmarks.EAS.EAS.FixedAllocate

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easAllocate128 {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {heap ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+5 ≤ 1024) (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4695⟩ (heap::ret::R) mem aw rdata σ k C) :
    if allocateNext heap.toNat 128 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 128 then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret R
        (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat 128))) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases hg : allocateNext heap.toNat 128 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 128
  · rw [if_pos hg]
    exact easFixedAllocate_ok v .bytes128 hstack hg hvalid rd
  · rw [if_neg hg]
    exact easFixedAllocate_revert v .bytes128 (by simp only [List.length_cons]; omega) hg rd

end Benchmarks.EAS.EAS

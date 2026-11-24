import Benchmarks.EAS.EAS.TypedDataMemory
import Benchmarks.EAS.EAS.BuildDomainEVM
import Benchmarks.EAS.EAS.RuntimeBlocks_049

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem typedDataEVM {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap domain structHash ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+9 ≤ 1024) (hh : memLoad (UInt256.ofNat 64) mem = heap)
    (hlo : 96 ≤ heap.toNat) (hheap : heap.toNat ≤ 2^64-1)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨15654⟩ (domain::structHash::ret::R) mem aw rdata σ k C) :
    if allocateNext heap.toNat 128 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 128 then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (typedDataWord domain structHash::R)
        (typedDataMemory mem heap.toNat domain structHash) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  obtain ⟨aw1,k1,C1,r1⟩ := easBlocks.eas_block_15654_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_15654_stack,hh] at r1
  split_ifs with hg
  · obtain ⟨aw2,k2,C2,r2⟩ := easAllocate_ok (heap := heap) (size := UInt256.ofNat 98)
      (ret := UInt256.ofNat 14209) (R := heap::(heap+UInt256.ofNat 32)::ret::R) v
      (by simp only [List.length_cons]; omega) hg (by rw [easPatchedValidJumps v]; jump_dest) r1
    have hb : heap.toNat+128 < UInt256.size := by change heap.toNat+128 < 2^256; omega
    have hoff (n : Nat) (hn : n ≤ 128) : (heap+UInt256.ofNat n).toNat = heap.toNat+n := uadd_word_ofNat_toNat heap n (by omega)
    have hm : Reasoning.Theory.writeWord
        (easBlocks.eas_block_15654_memory (mem := mem) (x0 := domain) (x1 := structHash))
        64 (UInt256.ofNat (allocateNext heap.toNat 98)) = typedDataMemory mem heap.toNat domain structHash := by
      simp only [easBlocks.eas_block_15654_memory,hh,hoff 32 (by decide),hoff 34 (by decide),hoff 66 (by decide),
        typedDataMemory,typedDataBuffer,writeWordSequence,Reasoning.Theory.writeWord,Nat.add_assoc,Nat.reduceAdd]
      rfl
    change RD fork _ _ _ _ ⟨14209⟩ (heap::(heap+UInt256.ofNat 32)::ret::R)
      (Reasoning.Theory.writeWord _ 64 (UInt256.ofNat (allocateNext heap.toNat 98))) _ _ _ _ _ at r2
    rw [hm] at r2
    obtain ⟨aw3,k3,C3,r3⟩ := easBlocks.eas_block_14209_packed (immWords := wordsOf (immStore v)) (by omega) hret r2
    refine ⟨aw3,k3,C3,?_⟩
    simpa only [easBlocks.eas_block_14209_stack,typedDataMemory_keccak mem heap domain structHash hlo (by omega)] using r3
  · exact easAllocate_revert (heap := heap) (size := UInt256.ofNat 98)
      (R := UInt256.ofNat 14209::heap::(heap+UInt256.ofNat 32)::ret::R) v
      (by simp only [List.length_cons]; omega) hg r1

end Benchmarks.EAS.EAS

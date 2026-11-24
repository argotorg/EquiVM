import Benchmarks.EAS.EAS.ArrayAllocationHead
import Benchmarks.EAS.EAS.RuntimeBlocks_027

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def wordArrayAllocationMemory (mem calldata : ByteArray) (heap : UInt256) (len : Nat) : ByteArray :=
  calldata.write calldata.size
    (Reasoning.Theory.writeWord
      (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat (32+32*len))))
      heap.toNat (UInt256.ofNat len)) (heap.toNat+32) (32*len)

-- LIBRARY CANDIDATE: remove the length word from a word-array allocation size modulo 2^256.
theorem wordArraySize_sub32 (n : Nat) :
    UInt256.ofNat (32+32*n) + UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 =
      UInt256.ofNat (32*n) := by
  rw [show UInt256.ofNat (32+32*n) = (⟨32⟩ : UInt256)+UInt256.ofNat (32*n) from by
    simpa only [Nat.add_comm] using (u256_32_add_ofNat (32*n)).symm]
  rw [u256_add_comm (⟨32⟩ : UInt256),u256_add_assoc,
    show (⟨32⟩ : UInt256)+UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 = ⟨0⟩ from rfl,
    u256_add_zero]

theorem easWordArrayAllocate {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap len ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+10 ≤ 1024)
    (hh : heap.toNat ≤ 2^64-1) (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hcd : ee.calldata.size < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨7240⟩ (len::ret::R) mem aw rdata σ k C) :
    if len.toNat ≤ 2^64-1 then
      if allocateNext heap.toNat (32+32*len.toNat) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (32+32*len.toNat) then
        ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (heap::R)
          (wordArrayAllocationMemory mem ee.calldata heap len.toNat) aw' rdata σ k' C'
      else RDrev fork (deployedRuntime v) g s0
    else RDrev fork (deployedRuntime v) g s0 := by
  have hhead := easArrayAllocationHead v .words hstack hheap rd
  by_cases hl : len.toNat ≤ 2^64-1
  · rw [if_pos hl] at hhead ⊢
    by_cases hg : allocateNext heap.toNat (32+32*len.toNat) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (32+32*len.toNat)
    · rw [if_pos hg] at hhead ⊢
      obtain ⟨a1,k1,C1,r1⟩ := hhead
      obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_7309_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hret r1
      refine ⟨a2,k2,C2,?_⟩
      simpa only [easBlocks.eas_block_7309_stack,easBlocks.eas_block_7309_memory,arrayAllocationHeaderMemory,
        wordArrayAllocationMemory,Reasoning.Theory.writeWord,ulit_toNat' _ hcd,wordArraySize_sub32,
        ulit_toNat' (32*len.toNat) (by change 32*len.toNat < 2^256; omega),
        uadd_word_ofNat_toNat heap 32 (by change heap.toNat+32 < 2^256; omega),u256_ofNat_toNat] using r2
    · simpa only [if_neg hg] using hhead
  · simpa only [if_neg hl] using hhead

end Benchmarks.EAS.EAS

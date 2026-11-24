import Benchmarks.EAS.EAS.BatchArrayDecode
import Benchmarks.EAS.EAS.ArrayTableAllocate
import Benchmarks.EAS.EAS.RuntimeBlocks_015

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

set_option maxHeartbeats 1000000 in
theorem easMultiAttestDecode {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+8 ≤ 1024) (hsize : ee.calldata.size < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨3682⟩ R mem aw rdata σ k C) :
    if wordArrayValid ee.calldata then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨3713⟩
        (UInt256.ofNat (wordArrayLength ee.calldata)::UInt256.ofNat (wordArrayOffset ee.calldata+36)::R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  exact easBatchArrayDecode v .attest hstack hsize rd

def multiAttestLoopStack (n i : Nat) (base table available count : UInt256) (R : List UInt256) : List UInt256 :=
  UInt256.ofNat n::(UInt256.ofNat n-⟨1⟩)::available::base::UInt256.ofNat i::table::count::R

theorem easMultiAttestAllocate {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C n : Nat}
    {base heap : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+12 ≤ 1024)
    (hn : n ≤ 2^64-1) (hh : heap.toNat ≤ 2^64-1) (hf : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨3713⟩ (UInt256.ofNat n::base::R) mem aw rdata σ k C) :
    if allocateNext heap.toNat (32+32*n) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (32+32*n) then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨3767⟩
        (multiAttestLoopStack n 0 base heap ee.weiValue ⟨0⟩ R)
        (arrayTableAllocationMemory mem heap n) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have hn' : (UInt256.ofNat n).toNat = n := ulit_toNat' _ (by change n < 2^256; omega)
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_3713_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  have ha := easArrayTableAllocate v (by simp only [List.length_cons]; omega) hh hf
    (by rw [easPatchedValidJumps v]; jump_dest) r1
  simp only [hn',if_pos hn] at ha
  split <;> rename_i hg
  · rw [if_pos hg] at ha
    obtain ⟨a2,k2,C2,r2⟩ := ha
    obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_3722_packed (immWords := wordsOf (immStore v))
      (by omega) r2
    refine ⟨a3,k3,C3,?_⟩
    have hm : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 = UInt256.lnot ⟨0⟩ := by decide
    simpa only [easBlocks.eas_block_3722_stack,multiAttestLoopStack,hm,u256_add_lnot_zero_eq_sub_one] using r3
  · simpa only [if_neg hg] using ha

end Benchmarks.EAS.EAS

import Benchmarks.EAS.EAS.ReferenceTail
import Benchmarks.EAS.EAS.FixedAllocate
import Benchmarks.EAS.EAS.RevocationCopyMemory
import Benchmarks.EAS.EAS.RuntimeBlocks_023

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easRevokeCalldataCopy {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+9 ≤ 1024)
    (hsize : ee.calldata.size < UInt256.size) (h100 : 100 ≤ ee.calldata.size)
    (hbig : ee.calldata.size < 2^255+4) (hh : heap.toNat ≤ 2^64-1)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5854⟩ (UInt256.ofNat ee.calldata.size::ret::R) mem aw rdata σ k C) :
    if heap.toNat+64 ≤ 2^64-1 then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (heap::R)
        (revocationRecordMemory mem heap (revocationDataRecord ee.calldata 36)) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have hsub : UInt256.ofNat ee.calldata.size+UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639900 =
      UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨36⟩ := by
    change _ = UInt256.ofNat ee.calldata.size-⟨36⟩
    rw [word_sub_eq_add_neg (UInt256.ofNat ee.calldata.size) ⟨36⟩]; rfl
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5854_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by
      rw [hsub]
      exact solcDecodeLenCheckOk (head := ⟨36⟩) (need := ⟨64⟩)
        (by change 100 ≤ _; exact h100) (by change ee.calldata.size < 2^255+36; omega) hsize (by decide)) rd
  obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_5897_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
  simp only [easBlocks.eas_block_5897_stack,hheap] at r2
  have hn : allocateNext heap.toNat 64 = heap.toNat+64 := fixedAllocation_next .bytes64 hh
  by_cases hg : heap.toNat+64 ≤ 2^64-1
  · rw [if_pos hg]
    obtain ⟨a3,k3,C3,r3⟩ := easFixedAllocate_ok v .bytes64
      (by simp only [List.length_cons]; omega) (by rw [FixedAllocationSite.size,hn]; exact ⟨hg,by omega⟩)
      (by rw [easPatchedValidJumps v]; jump_dest) r2
    simp only [FixedAllocationSite.size,hn] at r3
    obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_5909_packed (immWords := wordsOf (immStore v))
      (by omega) hret r3
    have hm : easBlocks.eas_block_5909_memory (ee := ee) (x1 := heap)
        (mem := Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (heap.toNat+64))) =
        revocationRecordMemory mem heap (revocationDataRecord ee.calldata 36) := by
      simp only [revocationRecordMemory,writeWordSequence,revocationDataRecord,easBlocks.eas_block_5909_memory,
        ← writeWord_as_write,uadd_word_ofNat_toNat heap 32 (by change heap.toNat+32 < 2^256; omega)]
      rfl
    rw [hm] at r4
    exact ⟨a4,k4,C4,r4⟩
  · rw [if_neg hg]
    exact easFixedAllocate_revert v .bytes64 (by simp only [List.length_cons]; omega)
      (by rw [FixedAllocationSite.size,hn]; intro h; exact hg h.1) r2

end Benchmarks.EAS.EAS

import Benchmarks.EAS.EAS.DelegatedRevocationMemory
import Benchmarks.EAS.EAS.DelegatedRevokeRecordMemory
import Benchmarks.EAS.EAS.MemoryArrayIndex
import Benchmarks.EAS.EAS.FixedAllocate

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def DelegatedRevocationBatch.request (r : DelegatedRevocationBatch) (j : Nat)
    (hd : j < r.data.length) (hs : j < r.signatures.length) : DelegatedRevocationRecord :=
  ⟨r.schema,r.data[j],r.signatures[j],r.revoker⟩

def multiDelegatedRevokeVerifyStack (j : Nat) (base n available last row data : UInt256) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat j,base,n,available,row+UInt256.ofNat 96,row+UInt256.ofNat 64,data,last,row]++R

theorem easMultiDelegatedRevokeVerifyPrepare {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap row data sig base n available last : UInt256} {j : Nat} {R : List UInt256}
    {r : DelegatedRevocationBatch} (v : EASImmutables)
    (hstack : R.length+24 ≤ 1024) (hv : DelegatedRevocationBatchMemoryView mem row data sig r heap.toNat)
    (hh : heap.toNat ≤ 2^64-1) (hf : memLoad (UInt256.ofNat 64) mem = heap)
    (hj : j < r.data.length) (hjs : j < r.signatures.length)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1552⟩
      (multiDelegatedRevokeVerifyStack j base n available last row data R) mem aw rdata σ k C) :
    if heap.toNat+128 ≤ 2^64-1 then
      ∃ (mem' : ByteArray) (dp sp aw' : UInt256) (k' C' : Nat),
        MemoryPrefix mem mem' heap.toNat ∧
        DelegatedRevokeMemoryView mem' heap dp sp (r.request j hj hjs) (heap.toNat+128) ∧
        memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat (heap.toNat+128) ∧
        RD fork (deployedRuntime v) ee g s0 ⟨13806⟩
          ([heap,UInt256.ofNat 1652,UInt256.ofNat j,UInt256.ofNat 1,base,n,available,
            row+UInt256.ofNat 96,row+UInt256.ofNat 64,data,last,row]++R) mem' aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  simp only [multiDelegatedRevokeVerifyStack,List.cons_append,List.nil_append] at rd
  have hdspan := hv.data.span
  have hsspan := hv.signatures.span
  have hlen : r.data.length < UInt256.size := by change _ < 2^256; omega
  have hslen : r.signatures.length < UInt256.size := by change _ < 2^256; omega
  have hjn : j < UInt256.size := by omega
  have hjp : 32*j < UInt256.size := by change _ < 2^256; omega
  obtain ⟨dp,hdp,hdv,hde,hdl⟩ := hv.data.elements j hj
  obtain ⟨sp,hsp,hsv,hse,hsl⟩ := hv.signatures.elements j hjs
  have hb : heap.toNat+128 < UInt256.size := by change _ < 2^256; omega
  have hlo : 96 ≤ heap.toNat := by have := hv.low; have := hv.span; omega
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_1552_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [hv.data.length,ult_one (by rw [ulit_toNat' _ hjn,ulit_toNat' _ hlen]; exact hj)]; decide) rd
  obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_1562_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
  simp only [easBlocks.eas_block_1562_stack,hv.schema] at r2
  obtain ⟨a3,k3,C3,r3⟩ := easMemoryArrayIndex v (by simp only [List.length_cons]; omega) hj hlen hjp
    hv.data.length (by rw [easPatchedValidJumps v]; jump_dest) r2
  obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_1579_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r3
  simp only [easBlocks.eas_block_1579_stack,hv.sigPointer,hdp] at r4
  obtain ⟨a5,k5,C5,r5⟩ := easMemoryArrayIndex v (by simp only [List.length_cons]; omega) hjs hslen hjp
    hv.signatures.length (by rw [easPatchedValidJumps v]; jump_dest) r4
  obtain ⟨a6,k6,C6,r6⟩ := easBlocks.eas_block_1591_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r5
  have hac : UInt256.land (UInt256.ofNat r.revoker.val) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) =
      UInt256.ofNat r.revoker.val := addressWord_val_clean r.revoker
  simp only [easBlocks.eas_block_1591_stack,hsp,hv.revoker,hf,hac] at r6
  have hn := allocateNext_128 hh
  by_cases hg : heap.toNat+128 ≤ 2^64-1
  · rw [if_pos hg]
    obtain ⟨a7,k7,C7,r7⟩ := easFixedAllocate_ok (heap := heap) v .bytes128 (by simp only [List.length_cons]; omega)
      (by change allocateNext heap.toNat 128 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 128; rw [hn]; exact ⟨hg,by omega⟩)
      (by rw [easPatchedValidJumps v]; jump_dest) r6
    change RD fork _ _ _ _ _ _ (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat 128))) _ _ _ _ _ at r7
    rw [hn] at r7
    obtain ⟨a8,k8,C8,r8⟩ := easBlocks.eas_block_1630_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r7
    have hm : easBlocks.eas_block_1630_memory
        (mem := Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (heap.toNat+128)))
        (x0 := r.schema) (x1 := dp) (x2 := sp) (x3 := UInt256.ofNat r.revoker.val) (x4 := heap) =
        delegatedRevokeRecordMemory mem heap dp sp (r.request j hj hjs) := by
      simp only [easBlocks.eas_block_1630_memory,delegatedRevokeRecordMemory,DelegatedRevocationBatch.request,
        writeWordSequence,Reasoning.Theory.writeWord,uadd_word_ofNat_toNat heap 32 (by omega),
        uadd_word_ofNat_toNat heap 64 (by omega),uadd_word_ofNat_toNat heap 96 (by omega),Nat.add_assoc]
    have hfacts := delegatedRevokeRecordMemory_facts (mem := mem) (heap := heap) (data := dp) (sig := sp)
      (r := r.request j hj hjs) hlo hb hdv hde hsv hse
    refine ⟨_,dp,sp,a8,k8,C8,hfacts.1,hfacts.2.1,hfacts.2.2,?_⟩
    simpa only [easBlocks.eas_block_1630_stack,hm] using r8
  · rw [if_neg hg]
    exact easFixedAllocate_revert v .bytes128 (by simp only [List.length_cons]; omega)
      (by change ¬(allocateNext heap.toNat 128 ≤ _ ∧ _); rw [hn]; exact fun h => hg h.1) r6

end Benchmarks.EAS.EAS

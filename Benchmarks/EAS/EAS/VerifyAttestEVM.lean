import Benchmarks.EAS.EAS.VerifyAttestMemory
import Benchmarks.EAS.EAS.VerifyStatic

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem verifyAttestStart {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap ptr dataPtr bytesPtr sigPtr ret : UInt256} {R : List UInt256} {r : DelegatedAttestationRecord} (v : EASImmutables)
    (hstack : R.length+20 ≤ 1024) (hperm : ee.perm = true)
    (hv : DelegatedAttestMemoryView mem ptr dataPtr bytesPtr sigPtr r heap.toNat)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) (hheap : heap.toNat ≤ 2^64-1)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨13494⟩ (ptr::ret::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨4883⟩
      (heap::⟨288⟩::⟨13715⟩::heap::(heap+UInt256.ofNat 32)::⟨13723⟩::sigPtr::⟨13745⟩::
        (ptr+UInt256.ofNat 96)::solcAddrMask::solcAddrMask::⟨13753⟩::ret::R)
      (verifyAttestBuffer mem heap.toNat r (solcSlotWord σ ee (nonceSlot r.attester))) aw' rdata
      (sstoreAccountMap ee.codeOwner σ (nonceSlot r.attester) (solcSlotWord σ ee (nonceSlot r.attester)+UInt256.ofNat 1)) k' C' := by
  have hb : heap.toNat+288 < UInt256.size := by change heap.toNat+288 < 2^256; omega
  obtain ⟨aw1,k1,C1,r1⟩ := easBlocks.eas_block_13494_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hperm rd
  rw [verifyAttestFirstStack hv,verifyAttestFirstMemory hv] at r1
  have howner : UInt256.land (memLoad (ptr+UInt256.ofNat 96) mem)
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = UInt256.ofNat r.attester.val := hv.attester
  simp only [howner] at r1
  change RD fork (deployedRuntime v) ee g s0 (UInt256.ofNat 13605) _ _ aw1 rdata
    (sstoreAccountMap ee.codeOwner σ
      (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (verifyAttestScratch mem r))
      (solcSlotWord σ ee (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (verifyAttestScratch mem r))+UInt256.ofNat 1)) k1 C1 at r1
  rw [verifyAttestScratch_slot mem r] at r1
  have hfree : memLoad (UInt256.ofNat 64) (verifyAttestScratch mem r) = heap :=
    twoWordHashMem_heap _ _ _ _ (by have := hv.low; have := hv.covered; omega) hh
  obtain ⟨aw2,k2,C2,r2⟩ := easBlocks.eas_block_13605_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
  rw [easBlocks.eas_block_13605_stack,hfree,verifyAttestLastMemory hv hh hb] at r2
  exact ⟨_,_,_,r2⟩

theorem verifyAttestHashEVM {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap ptr dataPtr bytesPtr sigPtr ret : UInt256} {R : List UInt256} {r : DelegatedAttestationRecord} (v : EASImmutables)
    (hstack : R.length+20 ≤ 1024) (hperm : ee.perm = true)
    (hv : DelegatedAttestMemoryView mem ptr dataPtr bytesPtr sigPtr r heap.toNat)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) (hheap : heap.toNat ≤ 2^64-1)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨13494⟩ (ptr::ret::R) mem aw rdata σ k C) :
    if allocateNext heap.toNat 288 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 288 then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨15646⟩
        (verifyAttestHash r (solcSlotWord σ ee (nonceSlot r.attester))::⟨13723⟩::sigPtr::⟨13745⟩::
          (ptr+UInt256.ofNat 96)::solcAddrMask::solcAddrMask::⟨13753⟩::ret::R)
        (verifyBuffer (verifyAttestScratch mem r) heap.toNat (verifyAttestWords r (solcSlotWord σ ee (nonceSlot r.attester)))) aw' rdata
        (sstoreAccountMap ee.codeOwner σ (nonceSlot r.attester) (solcSlotWord σ ee (nonceSlot r.attester)+UInt256.ofNat 1)) k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  obtain ⟨aw1,k1,C1,r1⟩ := verifyAttestStart v hstack hperm hv hh hheap rd
  split_ifs with hg
  · obtain ⟨aw2,k2,C2,r2⟩ := easAllocate_ok (heap := heap) (size := UInt256.ofNat 288) v
      (by simp only [List.length_cons]; omega) hg (by rw [easPatchedValidJumps v]; jump_dest) r1
    change RD fork _ _ _ _ ⟨13715⟩ _
      (verifyBuffer (verifyAttestScratch mem r) heap.toNat (verifyAttestWords r (solcSlotWord σ ee (nonceSlot r.attester)))) _ _ _ _ _ at r2
    obtain ⟨aw3,k3,C3,r3⟩ := easBlocks.eas_block_13715_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
    have hhash := verifyBuffer_keccak (verifyAttestScratch mem r) heap (verifyAttestWords r (solcSlotWord σ ee (nonceSlot r.attester)))
      (by have := hv.low; have := hv.span; omega) (by change heap.toNat+32 < 2^256; omega)
      (by simp only [verifyAttestWords,ne_eq,List.cons_ne_nil,not_false_eq_true])
      (by simp only [verifyAttestWords,List.length_cons,List.length_nil]; omega)
    refine ⟨aw3,k3,C3,?_⟩
    simpa only [easBlocks.eas_block_13715_stack,hhash,verifyAttestHash,verifyAttestPayload] using r3
  · exact easAllocate_revert (heap := heap) (size := UInt256.ofNat 288) v
      (by simp only [List.length_cons]; omega) hg r1

end Benchmarks.EAS.EAS

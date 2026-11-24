import Benchmarks.EAS.EAS.DelegatedAttestBuildMemory
import Benchmarks.EAS.EAS.CalldataAddress6240
import Benchmarks.EAS.EAS.CopyRequestCall
import Benchmarks.EAS.EAS.RuntimeBlocks_012

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def delegatedAttestBuildStack (schema src sigOffset addrHead ret j : UInt256) (R : List UInt256) : List UInt256 :=
  [addrHead,UInt256.ofNat 2969,UInt256.ofNat 2992,sigOffset,UInt256.ofNat 3009,src,solcAddrMask,schema,ret,j,⟨1⟩]++R

theorem easDelegatedAttestBuild {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema src sigOffset addrHead heap ret j : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+25 ≤ 1024) (hsize : ee.calldata.size<2^255+4)
    (hlo : 96≤heap.toNat) (hh : heap.toNat≤2^64-1) (hmem : 96≤mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem=heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨6240⟩ (delegatedAttestBuildStack schema src sigOffset addrHead ret j R) mem aw rdata σ k C) :
    let sigSrc := UInt256.mul j (UInt256.ofNat 96)+sigOffset
    (delegatedAttestBuildValid ee.calldata src sigSrc addrHead heap →
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨13494⟩ (heap::ret::j::⟨1⟩::R)
        (delegatedAttestBuildMemory mem ee.calldata schema src sigSrc addrHead heap) aw' rdata σ k' C') ∧
    (¬delegatedAttestBuildValid ee.calldata src sigSrc addrHead heap → RDrev fork (deployedRuntime v) g s0) := by
  let sigSrc := UInt256.mul j (UInt256.ofNat 96)+sigOffset
  simp only [delegatedAttestBuildStack,List.cons_append,List.nil_append] at rd
  have haddr := easCalldataAddress6240 v (by simp only [List.length_cons];omega)
    (by rw [easPatchedValidJumps v];jump_dest) rd
  by_cases ha : (calldataWord ee.calldata addrHead.toNat).toNat<EVM.addressModulus
  · rw [if_pos ha] at haddr
    obtain ⟨a1,k1,C1,r1⟩ := haddr
    obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_2969_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons];omega) (by rw [easPatchedValidJumpsRuntime v];jump_dest) r1
    simp only [easBlocks.eas_block_2969_stack,hfree] at r2
    have hn128 := allocateNext_128 hh
    by_cases hg : heap.toNat+128≤2^64-1
    · obtain ⟨a3,k3,C3,r3⟩ := easFixedAllocate_ok v .bytes128 (by simp only [List.length_cons];omega)
        (by change allocateNext heap.toNat 128≤2^64-1 ∧ heap.toNat≤allocateNext heap.toNat 128;rw [hn128];exact ⟨hg,by omega⟩)
        (by rw [easPatchedValidJumps v];jump_dest) r2
      change RD fork _ _ _ _ _ _ (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat 128))) _ _ _ _ _ at r3
      rw [hn128] at r3
      obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_2983_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons];omega) (by rw [easPatchedValidJumpsRuntime v];jump_dest) r3
      simp only [easBlocks.eas_block_2983_stack,easBlocks.eas_block_2983_memory,← writeWord_as_write] at r4
      change RD fork (deployedRuntime v) ee g s0 ⟨5344⟩
        (src::UInt256.ofNat ee.calldata.size::UInt256.ofNat 2992::sigOffset::UInt256.ofNat 3009::
          calldataWord ee.calldata addrHead.toNat::solcAddrMask::heap::ret::j::⟨1⟩::R)
        (delegatedAttestBuildSchema mem heap schema) a4 rdata σ k4 C4 at r4
      let dp := delegatedAttestBuildData heap
      have hdp : dp.toNat=heap.toNat+128 := ulit_toNat' _ (by change _<2^256;omega)
      have hm := delegatedAttestBuildSchema_facts mem heap schema hlo (by change _<2^256;omega) hmem
      have hcopy := easCopyRequest_branches (heap := dp) v (by simp only [List.length_cons];omega)
        (by rw [hdp];omega) (by rw [hdp];exact hg) hm.2.1 (by rw [easPatchedValidJumps v];jump_dest) r4
      by_cases hc : requestCopyRunValid ee.calldata src (UInt256.ofNat ee.calldata.size) dp
      · have hd := requestCopyRunValid_data hc
        have hv := (requestCopyRunValid_iff hd).mp hc
        have hviews := requestCopyMemory_views (delegatedAttestBuildSchema mem heap schema) ee.calldata src dp
          (by rw [hdp];omega) (by rw [hdp];exact hg) hsize hd hv
        let next := delegatedAttestBuildCopyHeap ee.calldata src heap
        have hnext : next≤2^64-1 := by simpa only [hdp] using hv.2.2.1
        have hnn : (UInt256.ofNat next).toNat=next := ulit_toNat' _ (by change _<2^256;omega)
        obtain ⟨a5,k5,C5,r5⟩ := hcopy.1 hc
        obtain ⟨a6,k6,C6,r6⟩ := easBlocks.eas_block_2992_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons];omega) (by rw [easPatchedValidJumpsRuntime v];jump_dest) r5
        simp only [easBlocks.eas_block_2992_stack,easBlocks.eas_block_2992_memory,← writeWord_as_write,
          uadd_word_ofNat_toNat heap 32 (by change _<2^256;omega)] at r6
        change RD fork (deployedRuntime v) ee g s0 ⟨6273⟩
          (sigSrc::UInt256.ofNat ee.calldata.size::UInt256.ofNat 3009::calldataWord ee.calldata addrHead.toNat::
            solcAddrMask::heap::ret::j::⟨1⟩::R)
          (delegatedAttestBuildLinked mem ee.calldata schema src heap) a6 rdata σ k6 C6 at r6
        have hfree6 : memLoad (UInt256.ofNat 64) (delegatedAttestBuildLinked mem ee.calldata schema src heap)=UInt256.ofNat next := by
          unfold delegatedAttestBuildLinked
          rw [memLoad_write_below _ _ _ _ (by change 96≤_;omega) (by
            have hcov := hviews.2.1.covered
            rw [hdp] at hcov
            change 96≤(delegatedAttestBuildCopied mem ee.calldata schema src heap).size
            change heap.toNat+128+192≤(delegatedAttestBuildCopied mem ee.calldata schema src heap).size at hcov
            omega)]
          simpa only [hdp] using hviews.2.2.1
        have hsig := easSignatureCalldataCopy (heap := UInt256.ofNat next) v (by simp only [List.length_cons];omega)
          (by rw [hnn];exact hnext) hfree6 (by rw [easPatchedValidJumps v];jump_dest) r6
        by_cases hs : signatureAtValid ee.calldata sigSrc ∧ next+96≤2^64-1
        · obtain ⟨a7,k7,C7,r7⟩ := hsig.1 (by simpa only [hnn] using hs)
          obtain ⟨a8,k8,C8,r8⟩ := easBlocks.eas_block_3009_packed (immWords := wordsOf (immStore v))
            (by simp only [List.length_cons];omega) (by rw [easPatchedValidJumpsRuntime v];jump_dest) r7
          have hac : UInt256.land (calldataWord ee.calldata addrHead.toNat) solcAddrMask=
              UInt256.ofNat (AccountAddress.ofNat (calldataWord ee.calldata addrHead.toNat).toNat).val := by
            rw [solcAddrMask_clean ha]
            exact (addressWord_eq_ofNat_address ha).symm
          have hb : heap.toNat+128<UInt256.size := by change _<2^256;omega
          have hmem8 : easBlocks.eas_block_3009_memory
              (mem := delegatedAttestBuildSignature mem ee.calldata schema src sigSrc heap)
              (x0 := UInt256.ofNat next) (x1 := calldataWord ee.calldata addrHead.toNat) (x2 := solcAddrMask) (x3 := heap)=
              delegatedAttestBuildMemory mem ee.calldata schema src sigSrc addrHead heap := by
            simp only [easBlocks.eas_block_3009_memory,← writeWord_as_write,hac,
              uadd_word_ofNat_toNat heap 64 (by omega),uadd_word_ofNat_toNat heap 96 (by omega)]
            rfl
          refine ⟨fun _ => ⟨a8,k8,C8,?_⟩,fun h => (h ⟨ha,hg,hd,by simpa only [hdp] using hv,hs.1,hs.2⟩).elim⟩
          change RD fork _ _ _ _ _ _ (easBlocks.eas_block_3009_memory
            (mem := delegatedAttestBuildSignature mem ee.calldata schema src sigSrc heap)
            (x0 := UInt256.ofNat next) (x1 := calldataWord ee.calldata addrHead.toNat) (x2 := solcAddrMask) (x3 := heap)) _ _ _ _ _ at r8
          simpa only [easBlocks.eas_block_3009_stack,hmem8] using r8
        · exact ⟨fun h => (hs ⟨h.2.2.2.2.1,h.2.2.2.2.2⟩).elim,
            fun _ => hsig.2 (by simpa only [hnn] using hs)⟩
      · exact ⟨fun h => (hc ((requestCopyRunValid_iff h.2.2.1).mpr (by simpa only [hdp] using h.2.2.2.1))).elim,
          fun _ => hcopy.2 hc⟩
    · exact ⟨fun h => (hg h.2.1).elim,fun _ => easFixedAllocate_revert v .bytes128
        (by simp only [List.length_cons];omega)
        (by change ¬(allocateNext heap.toNat 128≤_ ∧ _);rw [hn128];exact fun h => hg h.1) r2⟩
  · rw [if_neg ha] at haddr
    exact ⟨fun h => (ha h.1).elim,fun _ => haddr⟩

end Benchmarks.EAS.EAS

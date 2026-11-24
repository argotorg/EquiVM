import Benchmarks.EAS.EAS.DelegatedRevocationPrepared
import Benchmarks.EAS.EAS.CopySignatureArrayDecodedRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easDelegatedRevocationPrepareValid {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {root heap a b c d : UInt256} {r : DelegatedRevocationBatch} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+27 ≤ 1024) (hsize : ee.calldata.size < 2^255)
    (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1) (hmem : 96 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (hdecode : decodeDelegatedRevocationAt ee.calldata root = some r)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1318⟩ (root::a::b::c::d::R) mem aw rdata σ k C) :
    if delegatedRevocationNext heap r ≤ 2^64-1 then
      DelegatedRevocationPrepared fork v ee g s0 mem rdata σ heap a b c d R r
    else RDrev fork (deployedRuntime v) g s0 := by
  obtain ⟨hhead,hfields⟩ := decodeDelegatedRevocationAt_facts hdecode
  obtain ⟨haData,hdData,haSig,hdSig,haAddr,hSchema,hRevoker⟩ := decodeDelegatedRevocationFields_facts hfields
  obtain ⟨hvData,hlData,hcData⟩ := decodeRevocationArray_facts (by omega) hdData
  have hlenData : r.data.length ≤ 2^64-1 := by rw [hlData]; exact hvData.1
  have hlenWord : calldataWord ee.calldata (delegatedBatchArray ee.calldata root 32).toNat = UInt256.ofNat r.data.length := by
    rw [hlData,u256_ofNat_toNat]
  let dp := delegatedRevocationDataPtr heap
  have hdp : dp.toNat = heap.toNat+128 := ulit_toNat' _ (by change heap.toNat+128 < 2^256; omega)
  have hreserve := easDelegatedRevocationReserve v (by omega) hh hfree rd
  by_cases hr : heap.toNat+128 ≤ 2^64-1
  · rw [if_pos ⟨hhead,hr⟩] at hreserve
    obtain ⟨a1,j1,D1,r1⟩ := hreserve
    have haccess := easDelegatedRevocationDataAccess v (by omega) r1
    rw [if_pos haData] at haccess
    obtain ⟨a2,j2,D2,r2⟩ := haccess
    rw [hlenWord,← hSchema] at r2
    let m0 := delegatedRevocationSchemaMemory (delegatedRevocationReservedMemory mem heap) heap r.schema
    have hf0 : memLoad (UInt256.ofNat 64) m0 = dp := delegatedRevocationSchemaMemory_free mem heap r.schema hlo
    have hm0 : 96 ≤ m0.size := by
      simp only [m0,delegatedRevocationSchemaMemory,delegatedRevocationReservedMemory,writeWord_sparse_size]
      omega
    have hcopy := copyRevocationArrayRunStrong (heap := dp) v (by simp only [List.length_cons]; omega)
      hcData hsize hlenData (by rw [hdp]; omega) (by rw [hdp]; exact hr) hf0 hm0
      (by rw [easPatchedValidJumps v]; jump_dest) r2
    rw [hdp,show heap.toNat+128+32+96*r.data.length = heap.toNat+160+96*r.data.length by omega] at hcopy
    by_cases hdcap : heap.toNat+160+96*r.data.length ≤ 2^64-1
    · rw [if_pos hdcap] at hcopy
      obtain ⟨m2,a3,j3,D3,hpData,hvCopied,hfData,r3⟩ := hcopy
      let sp := delegatedRevocationSigPtr heap r.data
      have hsp : sp.toNat = heap.toNat+160+96*r.data.length := ulit_toNat' _ (by change _ < 2^256; omega)
      have hDataView := delegatedRevocationDataMemory_of_copy (mem := delegatedRevocationReservedMemory mem heap)
        (copied := m2) (row := heap) (data := dp) (schema := r.schema) (rs := r.data)
        (heap := heap.toNat+160+96*r.data.length) hlo (by rw [hdp])
        (by change heap.toNat+160+96*r.data.length < 2^256; omega) (by rw [hdp]; exact hpData) hvCopied
      let m3 := delegatedRevocationLinkData m2 heap dp
      have hData3 : DelegatedRevocationDataMemoryView m3 heap dp r.schema r.data sp.toNat := by
        rw [hsp]; exact hDataView
      have hm2 : 96 ≤ m2.size := by have hc := hvCopied.covered; have hl := hvCopied.low; omega
      have hf3 : memLoad (UInt256.ofNat 64) m3 = sp :=
        delegatedRevocationLinkData_free hlo (by change heap.toNat+32 < 2^256; omega) hm2 hfData
      have hm3 : 96 ≤ m3.size := by simp only [m3,delegatedRevocationLinkData,writeWord_sparse_size]; omega
      have hsigAccess := easDelegatedRevocationSignatureAccess v (by omega) r3
      rw [if_pos haSig] at hsigAccess
      obtain ⟨a4,j4,D4,r4⟩ := hsigAccess
      have hsigCopy := copySignatureArrayDecodedRun (heap := sp) v (by simp only [List.length_cons]; omega)
        hsize (by rw [hsp]; omega) (by rw [hsp]; exact hdcap) hf3 hm3 hdSig r4
      have hnext : sp.toNat+32+128*r.signatures.length = delegatedRevocationNext heap r := by
        rw [hsp]; unfold delegatedRevocationNext; omega
      rw [hnext] at hsigCopy
      by_cases ht : delegatedRevocationNext heap r ≤ 2^64-1
      · rw [if_pos ht] at hsigCopy ⊢
        obtain ⟨m4,a5,j5,D5,hpSig,hvSig,hfSig,r5⟩ := hsigCopy
        have htotal : delegatedRevocationNext heap r < UInt256.size := by change _ < 2^256; omega
        have hspNext : sp.toNat ≤ delegatedRevocationNext heap r := by rw [← hnext]; omega
        have hpSig0 : MemoryPrefix m3 m4 sp.toNat := (recordPadding_prefix m3 sp.toNat).trans hpSig
        have hData4 := hData3.preserve hpSig0 hspNext htotal
        have hassembled := delegatedRevocationAssembleMemory hData4 hvSig (by rw [hsp]; omega) htotal hfSig
        obtain ⟨hView,hFinalFree,hFinalPrefix⟩ := hassembled
        have haddr := easDelegatedRevocationAddressAccess v (by omega) r5
        rw [if_pos haAddr] at haddr
        obtain ⟨a6,j6,D6,r6⟩ := haddr
        have hword : calldataWord ee.calldata (root+UInt256.ofNat 96).toNat = UInt256.ofNat r.revoker.val := by
          rw [hRevoker]
          exact (addressWord_eq_ofNat_address haAddr).symm
        rw [hword] at r6
        let m5 := delegatedRevocationLinkSignatures m4 heap sp
        have hm4 : 96 ≤ m4.size := by have hc := hvSig.covered; have hl := hvSig.low; omega
        have hf5 : memLoad (UInt256.ofNat 64) m5 = UInt256.ofNat (delegatedRevocationNext heap r) :=
          delegatedRevocationLinkSignatures_free hlo (by change heap.toNat+64 < 2^256; omega) hm4 hfSig
        have hp0 : MemoryPrefix (recordPadding mem heap.toNat) m0 heap.toNat :=
          (recordPadding_low_write mem heap.toNat 64 (UInt256.ofNat (heap.toNat+128)) hmem (by decide)).trans
            (recordPadding_write_prefix _ heap.toNat r.schema
              (by rw [writeWord_sparse_size]; change 96 ≤ _; omega))
        have hpData0 : MemoryPrefix m0 m2 dp.toNat := by
          rw [hdp]
          exact (recordPadding_prefix m0 (heap.toNat+128)).trans hpData
        have hrow32 : (heap+UInt256.ofNat 32).toNat = heap.toNat+32 := uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
        have hp3 : MemoryPrefix m2 m3 heap.toNat :=
          memoryPrefix_sparse_writeWord m2 (heap+UInt256.ofNat 32).toNat heap.toNat dp (Or.inl (by rw [hrow32]; omega))
        refine ⟨m5,a6,j6,D6,?_,hView,hf5,hFinalFree,r6⟩
        exact (hp0.trans (hpData0.mono (by rw [hdp]; omega))).trans
          (hp3.trans ((hpSig0.mono (by rw [hsp]; omega)).trans hFinalPrefix))
      · rw [if_neg ht] at hsigCopy ⊢
        exact hsigCopy
    · rw [if_neg hdcap] at hcopy
      rw [if_neg (by unfold delegatedRevocationNext; omega)]
      exact hcopy
  · rw [if_neg (fun h => hr h.2)] at hreserve
    rw [if_neg (by unfold delegatedRevocationNext; omega)]
    exact hreserve

end Benchmarks.EAS.EAS

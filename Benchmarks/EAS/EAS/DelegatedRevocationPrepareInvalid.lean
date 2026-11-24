import Benchmarks.EAS.EAS.DelegatedRevocationPrepared
import Benchmarks.EAS.EAS.CopySignatureArrayDecodedRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easDelegatedRevocationPrepareInvalid {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {root heap a b c d : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+27 ≤ 1024) (hsize : ee.calldata.size < 2^255)
    (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1) (hmem : 96 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (hdecode : decodeDelegatedRevocationAt ee.calldata root = none)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1318⟩ (root::a::b::c::d::R) mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  let dp := delegatedRevocationDataPtr heap
  have hdp : dp.toNat = heap.toNat+128 := ulit_toNat' _ (by change heap.toNat+128 < 2^256; omega)
  have hreserve := easDelegatedRevocationReserve v (by omega) hh hfree rd
  split at hreserve
  · rename_i hr
    obtain ⟨a1,j1,D1,r1⟩ := hreserve
    have haccess := easDelegatedRevocationDataAccess v (by omega) r1
    split at haccess
    · rename_i haData
      obtain ⟨a2,j2,D2,r2⟩ := haccess
      let m0 := delegatedRevocationSchemaMemory (delegatedRevocationReservedMemory mem heap) heap (calldataWord ee.calldata root.toNat)
      have hf0 : memLoad (UInt256.ofNat 64) m0 = dp := delegatedRevocationSchemaMemory_free mem heap _ hlo
      have hm0 : 96 ≤ m0.size := by
        simp only [m0,delegatedRevocationSchemaMemory,delegatedRevocationReservedMemory,writeWord_sparse_size]
        omega
      cases hdData : decodeRevocationArray ee.calldata (delegatedBatchArray ee.calldata root 32) with
      | none =>
        exact easCopyRevocationArrayInvalid (heap := dp) v (by simp only [List.length_cons]; omega) hf0 hdData r2
      | some rs =>
        obtain ⟨hvData,hlData,hcData⟩ := decodeRevocationArray_facts (by omega) hdData
        have hlen : rs.length ≤ 2^64-1 := by rw [hlData]; exact hvData.1
        have hword : calldataWord ee.calldata (delegatedBatchArray ee.calldata root 32).toNat = UInt256.ofNat rs.length := by
          rw [hlData,u256_ofNat_toNat]
        rw [hword] at r2
        have hcopy := copyRevocationArrayRunStrong (heap := dp) v (by simp only [List.length_cons]; omega)
          hcData hsize hlen (by rw [hdp]; omega) (by rw [hdp]; exact hr.2) hf0 hm0
          (by rw [easPatchedValidJumps v]; jump_dest) r2
        rw [hdp,show heap.toNat+128+32+96*rs.length = heap.toNat+160+96*rs.length by omega] at hcopy
        split at hcopy
        · rename_i hdcap
          obtain ⟨m2,a3,j3,D3,hpData,hvCopied,hfData,r3⟩ := hcopy
          let sp := delegatedRevocationSigPtr heap rs
          have hsp : sp.toNat = heap.toNat+160+96*rs.length := ulit_toNat' _ (by change _ < 2^256; omega)
          let m3 := delegatedRevocationLinkData m2 heap dp
          have hm2 : 96 ≤ m2.size := by have hc := hvCopied.covered; have hl := hvCopied.low; omega
          have hf3 : memLoad (UInt256.ofNat 64) m3 = sp :=
            delegatedRevocationLinkData_free hlo (by change heap.toNat+32 < 2^256; omega) hm2 hfData
          have hm3 : 96 ≤ m3.size := by simp only [m3,delegatedRevocationLinkData,writeWord_sparse_size]; omega
          have hsigAccess := easDelegatedRevocationSignatureAccess v (by omega) r3
          split at hsigAccess
          · rename_i haSig
            obtain ⟨a4,j4,D4,r4⟩ := hsigAccess
            cases hdSig : decodeSignatureArray ee.calldata (delegatedBatchArray ee.calldata root 64) with
            | none =>
              exact copySignatureArrayInvalid (heap := sp) v (by simp only [List.length_cons]; omega)
                hsize (by rw [hsp]; omega) (by rw [hsp]; exact hdcap) hf3 hm3 hdSig r4
            | some ss =>
              by_cases haAddr : delegatedBatchAddressClean ee.calldata root
              · have he : decodeDelegatedRevocationAt ee.calldata root = some
                    (⟨calldataWord ee.calldata root.toNat,rs,ss,
                      AccountAddress.ofNat (calldataWord ee.calldata (root+UInt256.ofNat 96).toNat).toNat⟩ : DelegatedRevocationBatch) := by
                  rw [decodeDelegatedRevocationAt,if_pos hr.1,decodeDelegatedRevocationFields,
                    if_neg (not_not.mpr haData),hdData]
                  simp only [bind,Option.bind_some]
                  rw [if_neg (not_not.mpr haSig),hdSig]
                  simp only [Option.bind_some]
                  rw [if_neg (not_not.mpr haAddr)]
                rw [hdecode] at he
                cases he
              · have hsigCopy := copySignatureArrayDecodedRun (heap := sp) v (by simp only [List.length_cons]; omega)
                  hsize (by rw [hsp]; omega) (by rw [hsp]; exact hdcap) hf3 hm3 hdSig r4
                split at hsigCopy
                · obtain ⟨m4,a5,j5,D5,hpSig,hvSig,hfSig,r5⟩ := hsigCopy
                  have haddr := easDelegatedRevocationAddressAccess v (by omega) r5
                  simpa only [if_neg haAddr] using haddr
                · exact hsigCopy
          · exact hsigAccess
        · exact hcopy
    · exact haccess
  · exact hreserve

end Benchmarks.EAS.EAS

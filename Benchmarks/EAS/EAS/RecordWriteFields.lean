import Benchmarks.EAS.EAS.RecordOtherAccounts

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def recordBytesPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 8976
  | .many .. => UInt256.ofNat 11265
def recordBytesStack (site : UIDSite) (slot word src dataPtr len t1 t2 t3 t4 : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .single s1 s2 s3 s4 s5 s6 s7 s8 =>
      dataPtr :: len :: slot :: t3 :: word :: t2 :: src :: s5 :: s8 :: t1 :: s1 :: s2 :: t4 :: s6 :: s3 :: s4 :: s7 :: R
  | .many s1 s2 s3 s4 s5 s6 =>
      len :: slot :: s6 :: word :: dataPtr :: t2 :: src :: t1 :: s5 :: t3 :: t4 :: s1 :: s2 :: s3 :: s4 :: R

theorem easRecordWriteFields {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src dataPtr slot word t1 t2 t3 t4 : UInt256} {a : AttestationRecord} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+22 ≤ 1024) (hperm : ee.perm = true)
    (hv : AttestationMemoryView mem src dataPtr a) (hlen : a.data.size < 2^64)
    (rd : RD fork (deployedRuntime v) ee g s0 (recordFieldsPC site)
      (recordFieldsStack site slot word src t1 t2 t3 t4 R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (recordBytesPC site)
      (recordBytesStack site slot word src dataPtr (UInt256.ofNat a.data.size) t1 t2 t3 t4 R) mem aw' rdata
      (writeScalarAccounts ((attestationScalarWrites slot a).drop 5) σ ee) k' C' := by
  have hf := hv.fields
  simp only [attestationEncodeHeadWords,attestationEncodeFirstWords,attestationEncodeLastWords,
    AttestationRecord.words,List.cons_append,List.nil_append,List.cons.injEq,and_true] at hf
  obtain ⟨_,_,_,_,_,href,hrecipient,hattester,hbool⟩ := hf
  change UInt256.land (memLoad (src+UInt256.ofNat 192) mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = UInt256.ofNat a.recipient.val at hrecipient
  change UInt256.land (memLoad (src+UInt256.ofNat 224) mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = UInt256.ofNat a.attester.val at hattester
  have hcleanR : UInt256.land (UInt256.ofNat a.recipient.val) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = UInt256.ofNat a.recipient.val := addressWord_val_clean _
  have hcleanA : UInt256.land (UInt256.ofNat a.attester.val) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = UInt256.ofNat a.attester.val := addressWord_val_clean _
  have hrl := (u256_land_comm _ _).trans hrecipient
  have hal := (u256_land_comm _ _).trans hattester
  have hlen256 : a.data.size < UInt256.size := lt_trans hlen (by decide)
  have hc : UInt256.gt (memLoad (memLoad (src+UInt256.ofNat 288) mem) mem)
      (UInt256.ofNat 18446744073709551615) = UInt256.ofNat 0 := by
    rw [hv.pointer,hv.length]
    apply ugt_zero
    rw [ulit_toNat' _ hlen256]
    change a.data.size ≤ 18446744073709551615
    omega
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    obtain ⟨aw1,k1,C1,hr1⟩ := easBlocks.eas_block_8775_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hperm rd
    simp only [u256_add_comm (UInt256.ofNat 160) src,href,hrl,hal,hbool] at hr1
    change RD fork (deployedRuntime v) ee g s0 (UInt256.ofNat 8952)
      (recordFieldsStack (.single s1 s2 s3 s4 s5 s6 s7 s8) slot word src t1 t2 t3 t4 R)
      mem aw1 rdata (recordOtherSingleAccounts σ ee slot a) k1 C1 at hr1
    rw [← recordOtherAccounts_single,recordOtherAccounts_fields] at hr1
    obtain ⟨aw2,k2,C2,hr2⟩ := easBlocks.eas_block_8952_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hc hr1
    exact ⟨aw2,k2,C2,by simpa only [easBlocks.eas_block_8952_fallthrough_stack,hv.pointer,hv.length,
      recordBytesPC,recordBytesStack] using hr2⟩
  | many s1 s2 s3 s4 s5 s6 =>
    obtain ⟨aw1,k1,C1,hr1⟩ := easBlocks.eas_block_10990_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hperm rd
    simp only [easBlocks.eas_block_10990_stack,href,hrecipient,hattester,hbool,hcleanR,hcleanA] at hr1
    obtain ⟨aw2,k2,C2,hr2⟩ := easBlocks.eas_block_11240_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hperm hc hr1
    refine ⟨aw2,k2,C2,?_⟩
    rw [← recordOtherAccounts_fields]
    simp only [recordOtherAccounts,packedSliceWord_low,setLowWord_eq]
    rw [show UInt256.land (UInt256.ofNat a.recipient.val) (UInt256.ofNat (2^160-1)) = UInt256.ofNat a.recipient.val from hcleanR,
      show UInt256.land (UInt256.ofNat a.attester.val) (UInt256.ofNat (2^160-1)) = UInt256.ofNat a.attester.val from hcleanA]
    simpa only [easBlocks.eas_block_11240_fallthrough_stack,hv.pointer,hv.length,recordBytesPC,recordBytesStack,
      packedSliceWord] using hr2

end Benchmarks.EAS.EAS

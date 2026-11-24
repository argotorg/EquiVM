import Benchmarks.EAS.EAS.CopySignatureArrayHead
import Benchmarks.EAS.EAS.PaddingLowWrite

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem copySignatureArrayRun {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {header heap a b c d e : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+21 ≤ 1024)
    (hsize : ee.calldata.size < 2^255) (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap) (hmem : 96 ≤ mem.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1439⟩ (a::b::c::d::e::header::R) mem aw rdata σ k C) :
    let len := (calldataWord ee.calldata header.toNat).toNat
    let offset := header+UInt256.ofNat 32
    let ss := signatureRecords ee.calldata offset.toNat len
    if signatureArrayHeaderValid ee.calldata header ∧ (∀ s∈ss,signatureClean s) ∧ heap.toNat+32+128*len ≤ 2^64-1 then
      ∃ mem' aw' k' C', MemoryPrefix (recordPadding mem heap.toNat) mem' heap.toNat ∧
        CopySignatureArrayMemory mem' heap ss ss.length (heap.toNat+32+128*len) ∧
        memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat (heap.toNat+32+128*len) ∧
        RD fork (deployedRuntime v) ee g s0 ⟨1500⟩
          (UInt256.ofNat (heap.toNat+32+32*len)::UInt256.ofNat (offset.toNat+96*len)::
            UInt256.ofNat (offset.toNat+96*len)::a::b::c::d::e::heap::R) mem' aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  dsimp only
  let len := (calldataWord ee.calldata header.toNat).toNat
  let offset := header+UInt256.ofNat 32
  let ss := signatureRecords ee.calldata offset.toNat len
  have hlen : ss.length = len := signatureRecords_length _ _ _
  have hhead := easCopySignatureArrayHead v (by omega) hfree rd
  dsimp only at hhead
  by_cases hv : signatureArrayHeaderValid ee.calldata header
  · have hl : len ≤ 2^64-1 := hv.1
    have hb : offset.toNat+96*len ≤ ee.calldata.size := hv.extent (by omega)
    rw [allocateNext_wordArray hh hl] at hhead
    by_cases ht : heap.toNat+32+32*len ≤ 2^64-1
    · rw [if_pos ⟨hv,ht,by omega⟩] at hhead
      obtain ⟨a1,j1,D1,r1⟩ := hhead
      have hdptr : heap+UInt256.ofNat 32 = UInt256.ofNat (heap.toNat+32) := by
        apply u256_inj
        rw [uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega),ulit_toNat' _ (by change _ < 2^256; omega)]
      have hend : offset+UInt256.mul (calldataWord ee.calldata header.toNat) (UInt256.ofNat 96) =
          UInt256.ofNat (offset.toNat+96*len) := by
        rw [wordMul_nat _ 96 (by decide)]
        apply u256_inj
        rw [uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega),ulit_toNat' _ (by change _ < 2^256; omega)]
      rw [hdptr,hend] at r1
      obtain ⟨hp0,hm0,hf0⟩ := pointerTablePrefix_init SignatureCopyRegion mem heap ss hlo hh (by rw [hlen]; exact hl)
      rw [hlen,allocateNext_wordArray hh hl] at hm0 hf0
      have hpadded : MemoryPrefix (recordPadding mem heap.toNat) (arrayAllocationHeaderMemory mem heap len) heap.toNat :=
        (recordPadding_low_write mem heap.toNat 64 (UInt256.ofNat (allocateNext heap.toNat (32+32*len))) hmem (by decide)).trans
          (recordPadding_write_prefix _ heap.toNat (UInt256.ofNat len) (by rw [writeWord_sparse_size]; omega))
      have rstart : RD fork (deployedRuntime v) ee g s0 ⟨1492⟩
          (UInt256.ofNat (heap.toNat+32+32*0)::UInt256.ofNat (offset.toNat+96*0)::
            UInt256.ofNat (offset.toNat+96*ss.length)::a::b::c::d::e::heap::R)
          (arrayAllocationHeaderMemory mem heap len) a1 rdata σ j1 D1 := by
        simpa only [hlen,Nat.mul_zero,Nat.add_zero,u256_ofNat_toNat] using r1
      have hloop := copySignatureArrayLoop (ss := ss) (i := 0) v (by simp only [List.length_cons]; omega)
        (by rw [hlen]; exact hb) (fun i hi => (signatureRecords_get _ _ _ i hi).symm) hsize
        ss.length (by omega) hm0 (by intros; omega) ht hf0 rstart
      rw [hlen,show heap.toNat+32+32*len+96*len = heap.toNat+32+128*len by omega] at hloop
      by_cases hg : (∀ s∈ss,signatureClean s) ∧ heap.toNat+32+128*len ≤ 2^64-1
      · rw [if_pos hg] at hloop
        rw [if_pos ⟨hv,hg⟩]
        obtain ⟨m2,a2,j2,D2,hp2,hv2,hf2,r2⟩ := hloop
        exact ⟨m2,a2,j2,D2,hpadded.trans hp2,by simpa only [signatureRecords_length] using hv2,hf2,r2⟩
      · rw [if_neg hg] at hloop
        rw [if_neg (fun h => hg h.2)]
        exact hloop
    · rw [if_neg (fun h => ht h.2.1)] at hhead
      rw [if_neg (fun h => ht (by have hcap := h.2.2; change heap.toNat+32+128*len ≤ 2^64-1 at hcap; omega))]
      exact hhead
  · rw [if_neg (fun h => hv h.1)] at hhead ⊢
    exact hhead

end Benchmarks.EAS.EAS

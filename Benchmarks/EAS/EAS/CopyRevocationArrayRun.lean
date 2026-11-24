import Benchmarks.EAS.EAS.CopyRevocationArrayLoop
import Benchmarks.EAS.EAS.PaddingLowWrite

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem copyRevocationArrayRunStrong {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {offset heap ret : UInt256} {rs : List RevocationRequestRecord} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+15 ≤ 1024)
    (hc : RevocationArrayCalldataView ee.calldata offset rs) (hsize : ee.calldata.size < 2^255)
    (hlen : rs.length ≤ 2^64-1) (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap) (hmem : 96 ≤ mem.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5924⟩
      (offset::UInt256.ofNat rs.length::UInt256.ofNat ee.calldata.size::ret::R) mem aw rdata σ k C) :
    if heap.toNat+32+96*rs.length ≤ 2^64-1 then
      ∃ mem' aw' k' C', MemoryPrefix (recordPadding mem heap.toNat) mem' heap.toNat ∧
        CopyRevocationArrayMemory mem' heap rs rs.length (heap.toNat+32+96*rs.length) ∧
        memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat (heap.toNat+32+96*rs.length) ∧
        RD fork (deployedRuntime v) ee g s0 ret (heap::R) mem' aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have hb := hc.extent
  have hlenw : (UInt256.ofNat rs.length).toNat = rs.length := ulit_toNat' _ (by change _ < 2^256; omega)
  have he : offset+UInt256.shiftLeft (UInt256.ofNat rs.length) (UInt256.ofNat 6) =
      UInt256.ofNat (offset.toNat+64*rs.length) := by
    rw [wordShiftLeft_nat _ 6 (by decide),hlenw]
    change offset+UInt256.ofNat (64*rs.length) = _
    apply u256_inj
    rw [uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega),ulit_toNat' _ (by change _ < 2^256; omega)]
  have hg : UInt256.gt (offset+UInt256.shiftLeft (UInt256.ofNat rs.length) (UInt256.ofNat 6))
      (UInt256.ofNat ee.calldata.size) = ⟨0⟩ := by
    rw [he]
    apply ugt_zero
    rw [ulit_toNat' _ (by change _ < 2^256; omega),ulit_toNat' _ (by change _ < 2^256; omega)]
    exact hb
  have hhead := easCopyRevocationArrayHead v (by omega) hfree (by rw [hlenw]; exact hlen) hg rd
  rw [hlenw,allocateNext_wordArray hh hlen] at hhead
  by_cases ht : heap.toNat+32+32*rs.length ≤ 2^64-1
  · rw [if_pos ⟨ht,by omega⟩] at hhead
    obtain ⟨a1,k1,C1,r1⟩ := hhead
    rw [he] at r1
    have hdptr : heap+UInt256.ofNat 32 = UInt256.ofNat (heap.toNat+32) := by
      apply u256_inj
      rw [uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega),ulit_toNat' _ (by change _ < 2^256; omega)]
    rw [hdptr] at r1
    obtain ⟨hp0,hm0,hf0⟩ := pointerTablePrefix_init RevocationCopyRegion mem heap rs hlo hh hlen
    have hpadded : MemoryPrefix (recordPadding mem heap.toNat) (arrayAllocationHeaderMemory mem heap rs.length) heap.toNat :=
      (recordPadding_low_write mem heap.toNat 64 (UInt256.ofNat (allocateNext heap.toNat (32+32*rs.length))) hmem (by decide)).trans
        (recordPadding_write_prefix _ heap.toNat (UInt256.ofNat rs.length) (by rw [writeWord_sparse_size]; omega))
    rw [allocateNext_wordArray hh hlen] at hm0 hf0
    have rstart : RD fork (deployedRuntime v) ee g s0 ⟨5973⟩
        (UInt256.ofNat (heap.toNat+32+32*0)::UInt256.ofNat ee.calldata.size::
          UInt256.ofNat (offset.toNat+64*rs.length)::UInt256.ofNat (offset.toNat+64*0)::ret::heap::R)
        (arrayAllocationHeaderMemory mem heap rs.length) a1 rdata σ k1 C1 := by
      simpa only [Nat.mul_zero,Nat.add_zero,u256_ofNat_toNat] using r1
    have hloop := copyRevocationArrayLoopStrong v hstack hc hsize hret rs.length (by omega) hm0 ht hf0 rstart
    rw [show heap.toNat+32+32*rs.length+64*rs.length = heap.toNat+32+96*rs.length by omega] at hloop
    by_cases hall : heap.toNat+32+96*rs.length ≤ 2^64-1
    · rw [if_pos hall] at hloop ⊢
      obtain ⟨m2,a2,k2,C2,hp2,hv2,hf2,r2⟩ := hloop
      exact ⟨m2,a2,k2,C2,hpadded.trans hp2,hv2,hf2,r2⟩
    · rw [if_neg hall] at hloop ⊢
      exact hloop
  · rw [if_neg (fun h => ht h.1)] at hhead
    rw [if_neg (by omega : ¬ heap.toNat+32+96*rs.length ≤ 2^64-1)]
    exact hhead

theorem copyRevocationArrayRun {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {offset heap ret : UInt256} {rs : List RevocationRequestRecord} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+15 ≤ 1024)
    (hc : RevocationArrayCalldataView ee.calldata offset rs) (hsize : ee.calldata.size < 2^255)
    (hlen : rs.length ≤ 2^64-1) (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap) (hmem : 96 ≤ mem.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5924⟩
      (offset::UInt256.ofNat rs.length::UInt256.ofNat ee.calldata.size::ret::R) mem aw rdata σ k C) :
    if heap.toNat+32+96*rs.length ≤ 2^64-1 then
      ∃ mem' aw' k' C', MemoryPrefix (recordPadding mem heap.toNat) mem' heap.toNat ∧
        RevocationRequestArrayMemoryView mem' heap rs (heap.toNat+32+96*rs.length) ∧
        memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat (heap.toNat+32+96*rs.length) ∧
        RD fork (deployedRuntime v) ee g s0 ret (heap::R) mem' aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have h := copyRevocationArrayRunStrong v hstack hc hsize hlen hlo hh hfree hmem hret rd
  by_cases hg : heap.toNat+32+96*rs.length ≤ 2^64-1
  · rw [if_pos hg] at h ⊢
    obtain ⟨m,a,j,D,hp,hv,hf,hr⟩ := h
    exact ⟨m,a,j,D,hp,hv.finish,hf,hr⟩
  · simpa only [if_neg hg] using h

end Benchmarks.EAS.EAS

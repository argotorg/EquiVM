import Benchmarks.EAS.EAS.RequestArrayElements
import Benchmarks.EAS.EAS.CopyRequestArrayRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easCopyRequestArrayLoopReject {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {offset array heap ret : UInt256} {len i : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+23 ≤ 1024)
    (hc : offset.toNat+32*len ≤ ee.calldata.size) (hsize : ee.calldata.size < 2^255+4)
    (hlo : 96 ≤ array.toNat)
    (n : Nat) (hn : i+n = len)
    (hbad : decodeRequestElements ee.calldata offset i n = none)
    (hspan : array.toNat+32+32*len ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5594⟩
      (UInt256.ofNat (array.toNat+32+32*i)::UInt256.ofNat (offset.toNat+32*i)::offset::
        UInt256.ofNat (offset.toNat+32*len)::UInt256.ofNat ee.calldata.size::ret::array::R) mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  induction n generalizing i mem aw heap k C with
  | zero => rw [decodeRequestElements] at hbad; contradiction
  | succ n ih =>
    have hi : i < len := by omega
    have hsrc : (UInt256.ofNat (offset.toNat+32*i)).toNat = offset.toNat+32*i := ulit_toNat' _ (by change _ < 2^256; omega)
    have hend : (UInt256.ofNat (offset.toNat+32*len)).toNat = offset.toNat+32*len := ulit_toNat' _ (by change _ < 2^256; omega)
    have hdst : (UInt256.ofNat (array.toNat+32+32*i)).toNat = array.toNat+32+32*i := ulit_toNat' _ (by change _ < 2^256; omega)
    have hr := easCopyRequestArrayRead v (by omega) (by rw [hsrc,hend]; omega) rd
    by_cases ho : (calldataWord ee.calldata (offset.toNat+32*i)).toNat ≤ 2^64-1
    · obtain ⟨a1,k1,C1,r1⟩ := hr.1 (by rw [hsrc]; exact ho)
      rw [hsrc] at r1
      change RD fork (deployedRuntime v) ee g s0 ⟨5344⟩
        (requestArrayElement ee.calldata offset i::UInt256.ofNat ee.calldata.size::⟨5641⟩::UInt256.ofNat (array.toNat+32+32*i)::
          ⟨32⟩::⟨32⟩::UInt256.ofNat (offset.toNat+32*i)::offset::UInt256.ofNat (offset.toNat+32*len)::
          UInt256.ofNat ee.calldata.size::ret::array::R) mem a1 rdata σ k1 C1 at r1
      have hrun := easCopyRequest_branches v (by simp only [List.length_cons]; omega) (by omega) hh hfree
        (by rw [easPatchedValidJumps v]; jump_dest) r1
      by_cases hv : requestCopyRunValid ee.calldata (requestArrayElement ee.calldata offset i) (UInt256.ofNat ee.calldata.size) heap
      · have hd := requestCopyRunValid_data hv
        have hcopy := (requestCopyRunValid_iff hd).mp hv
        have ht : decodeRequestElements ee.calldata offset (i+1) n = none := by
          rw [decodeRequestElements,if_pos (show requestArrayElementValid ee.calldata offset i from ⟨ho,hd⟩)] at hbad
          cases ht : decodeRequestElements ee.calldata offset (i+1) n
          · rfl
          · rw [ht] at hbad; contradiction
        obtain ⟨a2,k2,C2,r2⟩ := hrun.1 hv
        let copied := requestCopyMemory mem ee.calldata (requestArrayElement ee.calldata offset i) heap
        let final := Reasoning.Theory.writeWord copied (array.toNat+32+32*i) heap
        let next := copyRequestNext heap.toNat (requestDataRecord ee.calldata (requestArrayElement ee.calldata offset i)).data.size
        have hm := requestCopyMemory_views mem ee.calldata (requestArrayElement ee.calldata offset i) heap (by omega) hh hsize hd hcopy
        have hnext : next ≤ 2^64-1 := hcopy.2.2.1
        have hheap : heap.toNat+192 ≤ next := hm.2.2.2.1
        have hcovered : next ≤ copied.size := hm.2.2.2.2.2
        have hnword : (UInt256.ofNat next).toNat = next := ulit_toNat' _ (by change _ < 2^256; omega)
        have hfnext : memLoad (UInt256.ofNat 64) final = UInt256.ofNat next :=
          (memLoad_write_below copied _ _ heap (by change 96 ≤ _; omega) (by change 96 ≤ copied.size; omega)).trans hm.2.2.1
        obtain ⟨a3,k3,C3,r3⟩ := easCopyRequestArraySet v (by simp only [List.length_cons]; omega) r2
        rw [hdst,wordStride32_next (array.toNat+32) i (by change _ < 2^256; omega),
          wordStride32_next offset.toNat i (by change _ < 2^256; omega)] at r3
        exact ih (by omega) ht (by rw [hnword]; omega) (by rw [hnword]; exact hnext) hfnext r3
      · exact hrun.2 hv
    · exact hr.2 (by rw [hsrc]; exact ho)

theorem easCopyRequestArrayReject {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {offset heap ret : UInt256} {len : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+23 ≤ 1024)
    (hc : offset.toNat+32*len ≤ ee.calldata.size) (hsize : ee.calldata.size < 2^255+4)
    (hbad : decodeRequestElements ee.calldata offset 0 len = none)
    (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5544⟩ (offset::UInt256.ofNat len::UInt256.ofNat ee.calldata.size::ret::R) mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  have hhead := easCopyRequestArrayHead v (by omega) hfree rd
  by_cases hv : requestArrayHeadValid offset (UInt256.ofNat len) (UInt256.ofNat ee.calldata.size) heap
  · obtain ⟨a1,k1,C1,r1⟩ := hhead.1 hv
    have hlen : (UInt256.ofNat len).toNat = len := ulit_toNat' _ (by change _ < 2^256; omega)
    have hl : len ≤ 2^64-1 := by simpa only [hlen] using hv.1
    have ha := hv.2.1
    rw [hlen] at ha r1
    have hshift : UInt256.shiftLeft (UInt256.ofNat len) (UInt256.ofNat 5) = UInt256.ofNat (32*len) :=
      shiftLeft5_ofNat_eq (by change _ < 2^256; omega)
    have he : offset+UInt256.shiftLeft (UInt256.ofNat len) (UInt256.ofNat 5) = UInt256.ofNat (offset.toNat+32*len) := by
      rw [hshift]
      apply u256_inj
      rw [uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega),ulit_toNat' _ (by change _ < 2^256; omega)]
    have hp : heap+UInt256.ofNat 32 = UInt256.ofNat (heap.toNat+32) := by
      apply u256_inj
      rw [uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega),ulit_toNat' _ (by change _ < 2^256; omega)]
    rw [he,hp] at r1
    let next := allocateNext heap.toNat (32+32*len)
    have hnword : (UInt256.ofNat next).toNat = next := ulit_toNat' _ (by have := ha.1; change _ < 2^256; omega)
    have hmem := copyRequestArrayMemory_init mem heap (List.replicate len (requestDataRecord ee.calldata offset)) hlo hh (by simpa only [List.length_replicate] using hl)
    simp only [List.length_replicate] at hmem
    apply easCopyRequestArrayLoopReject v hstack hc hsize hlo len (by omega) hbad
      (heap := UInt256.ofNat next) (by rw [hnword]; exact le_of_eq (allocateNext_wordArray hh hl).symm)
      (by rw [hnword]; exact ha.1) hmem.2.2
    simpa only [Nat.mul_zero,Nat.add_zero,u256_ofNat_toNat] using r1
  · exact hhead.2 hv

end Benchmarks.EAS.EAS

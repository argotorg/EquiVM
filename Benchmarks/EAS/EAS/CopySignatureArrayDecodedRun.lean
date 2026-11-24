import Benchmarks.EAS.EAS.CopySignatureArrayRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem copySignatureArrayDecodedRun {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {header heap a b c d e : UInt256} {ss : List SignatureRecord} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+21 ≤ 1024)
    (hsize : ee.calldata.size < 2^255) (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap) (hmem : 96 ≤ mem.size)
    (hd : decodeSignatureArray ee.calldata header = some ss)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1439⟩ (a::b::c::d::e::header::R) mem aw rdata σ k C) :
    if heap.toNat+32+128*ss.length ≤ 2^64-1 then
      ∃ mem' aw' k' C', MemoryPrefix (recordPadding mem heap.toNat) mem' heap.toNat ∧
        CopySignatureArrayMemory mem' heap ss ss.length (heap.toNat+32+128*ss.length) ∧
        memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat (heap.toNat+32+128*ss.length) ∧
        RD fork (deployedRuntime v) ee g s0 ⟨1500⟩
          (UInt256.ofNat (heap.toNat+32+32*ss.length)::
            UInt256.ofNat ((header+UInt256.ofNat 32).toNat+96*ss.length)::
            UInt256.ofNat ((header+UInt256.ofNat 32).toNat+96*ss.length)::a::b::c::d::e::heap::R) mem' aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have h := copySignatureArrayRun v hstack hsize hlo hh hfree hmem rd
  unfold decodeSignatureArray at hd
  split at hd
  · rename_i hheader
    dsimp only at hd
    split at hd
    · rename_i hclean
      have hss := Option.some.inj hd
      subst ss
      simpa only [hheader,iff_true_intro hclean,true_and,signatureRecords_length] using h
    · cases hd
  · cases hd

theorem copySignatureArrayInvalid {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {header heap a b c d e : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+21 ≤ 1024)
    (hsize : ee.calldata.size < 2^255) (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap) (hmem : 96 ≤ mem.size)
    (hd : decodeSignatureArray ee.calldata header = none)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1439⟩ (a::b::c::d::e::header::R) mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  have h := copySignatureArrayRun v hstack hsize hlo hh hfree hmem rd
  dsimp only at h
  split at h
  · rename_i hg
    have hd' : decodeSignatureArray ee.calldata header =
        some (signatureRecords ee.calldata (header+UInt256.ofNat 32).toNat (calldataWord ee.calldata header.toNat).toNat) := by
      rw [decodeSignatureArray,if_pos hg.1,if_pos hg.2.1]
    rw [hd] at hd'
    cases hd'
  · exact h

end Benchmarks.EAS.EAS

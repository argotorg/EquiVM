import Benchmarks.EAS.EAS.CopyRequestArraySource
import Benchmarks.EAS.EAS.CopyRequestArrayControl
import Benchmarks.EAS.EAS.CopyRequestArrayMemory

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def requestArrayElement (cd : ByteArray) (offset : UInt256) (i : Nat) : UInt256 :=
  offset+calldataWord cd (offset.toNat+32*i)

structure RequestArrayCalldataView (cd : ByteArray) (offset : UInt256) (rs : List AttestationRequestRecord) : Prop where
  extent : offset.toNat+32*rs.length ≤ cd.size
  requests : ∀ i (hi : i < rs.length),
    (calldataWord cd (offset.toNat+32*i)).toNat ≤ 2^64-1 ∧
    requestDataValid cd (requestArrayElement cd offset i) ∧
    requestDataRecord cd (requestArrayElement cd offset i) = rs[i]

-- LIBRARY CANDIDATE: advance a bounded 32-byte cursor by one element.
theorem wordStride32_next (base i : Nat) (hb : base+32*(i+1) < UInt256.size) :
    UInt256.ofNat (base+32*i)+⟨32⟩ = UInt256.ofNat (base+32*(i+1)) := by
  apply u256_inj
  rw [uadd_word_lit32_toNat _ (by rw [ulit_toNat' _ (by omega)]; omega),
    ulit_toNat' _ (by omega),ulit_toNat' _ hb]
  omega

theorem copyRequestArrayStepOfElement {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {offset array heap ret : UInt256} {rs : List AttestationRequestRecord} {i : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+23 ≤ 1024)
    (hf : CopyRequestArrayLocals L rs heap.toNat i) (hm : CopyRequestArrayMemory mem array rs i heap.toNat)
    (hcb : offset.toNat+32*rs.length ≤ ee.calldata.size) (hi : i < rs.length)
    (hrequest : (calldataWord ee.calldata (offset.toNat+32*i)).toNat ≤ 2^64-1 ∧
      requestDataValid ee.calldata (requestArrayElement ee.calldata offset i) ∧
      requestDataRecord ee.calldata (requestArrayElement ee.calldata offset i) = rs[i])
    (hh : heap.toNat ≤ 2^64-1) (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (hsize : ee.calldata.size < 2^255+4)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5594⟩
      (UInt256.ofNat (array.toNat+32+32*i)::UInt256.ofNat (offset.toNat+32*i)::offset::
        UInt256.ofNat (offset.toNat+32*rs.length)::UInt256.ofNat ee.calldata.size::ret::array::R) mem aw rdata σ k C) :
    (∃ L' mem' aw' k' C' next,
      heap.toNat ≤ next ∧ next ≤ 2^64-1 ∧ MemoryPrefix mem mem' array.toNat ∧
      CopyRequestArrayLocals L' rs next (i+1) ∧ CopyRequestArrayMemory mem' array rs (i+1) next ∧
      memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat next ∧
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm copyRequestArrayIteration
        (.ok {contract := contract,locals := L',immutables := immStore v} evm) ∧
      RD fork (deployedRuntime v) ee g s0 ⟨5594⟩
        (UInt256.ofNat (array.toNat+32+32*(i+1))::UInt256.ofNat (offset.toNat+32*(i+1))::offset::
          UInt256.ofNat (offset.toNat+32*rs.length)::UInt256.ofNat ee.calldata.size::ret::array::R) mem' aw' rdata σ k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm copyRequestArrayIteration .reverted ∧
      RDrev fork (deployedRuntime v) g s0) := by
  have hspan := hm.span
  have hlo : 96 ≤ heap.toNat := by have := hm.low; omega
  have hlen : rs.length < UInt256.size := by change _ < 2^256; omega
  have hsrc : (UInt256.ofNat (offset.toNat+32*i)).toNat = offset.toNat+32*i := ulit_toNat' _ (by change _ < 2^256; omega)
  have hend : (UInt256.ofNat (offset.toNat+32*rs.length)).toNat = offset.toNat+32*rs.length := ulit_toNat' _ (by change _ < 2^256; omega)
  have hdst : (UInt256.ofNat (array.toNat+32+32*i)).toNat = array.toNat+32+32*i := ulit_toNat' _ (by change _ < 2^256; omega)
  obtain ⟨ho,hd,he⟩ := hrequest
  obtain ⟨a1,k1,C1,r1⟩ := (easCopyRequestArrayRead v (by omega) (by rw [hsrc,hend]; omega) rd).1
    (by rw [hsrc]; exact ho)
  rw [hsrc] at r1
  change RD fork (deployedRuntime v) ee g s0 ⟨5344⟩
    (requestArrayElement ee.calldata offset i::UInt256.ofNat ee.calldata.size::⟨5641⟩::UInt256.ofNat (array.toNat+32+32*i)::
      ⟨32⟩::⟨32⟩::UInt256.ofNat (offset.toNat+32*i)::offset::UInt256.ofNat (offset.toNat+32*rs.length)::
      UInt256.ofNat ee.calldata.size::ret::array::R) mem a1 rdata σ k1 C1 at r1
  have hrun := easCopyRequest_branches v (by simp only [List.length_cons]; omega) hlo hh hfree
    (by rw [easPatchedValidJumps v]; jump_dest) r1
  have hg := requestCopyRunValid_iff (heap := heap) hd
  rw [he] at hg
  have hsol := copyRequestArrayIterationSource (fork := fork) (imms := immStore v) (evm := evm) hf hi hlen
  by_cases hv : copyRequestValid heap.toNat rs[i].data.size
  · obtain ⟨a2,k2,C2,r2⟩ := hrun.1 (hg.mpr hv)
    let copied := requestCopyMemory mem ee.calldata (requestArrayElement ee.calldata offset i) heap
    let final := Reasoning.Theory.writeWord copied (array.toNat+32+32*i) heap
    let next := copyRequestNext heap.toNat rs[i].data.size
    let dp := UInt256.ofNat (allocateNext heap.toNat 192)
    have hc0 := requestCopyMemory_views mem ee.calldata (requestArrayElement ee.calldata offset i) heap hlo hh hsize hd (by rw [he]; exact hv)
    dsimp only at hc0
    rw [he] at hc0
    change MemoryPrefix mem copied heap.toNat ∧ AttestationRequestMemoryView copied heap dp rs[i] ∧
      memLoad (UInt256.ofNat 64) copied = UInt256.ofNat next ∧ heap.toNat+192 ≤ next ∧
      dp.toNat+32+32*((rs[i].data.size+31)/32) = next ∧ next ≤ copied.size at hc0
    have hnext : next < UInt256.size := by have := hv.2.2.1; change _ < 2^256; omega
    have hn : heap.toNat ≤ next := by have := hc0.2.2.2.1; omega
    have hdp : dp.toNat = heap.toNat+192 := by
      dsimp only [dp]
      rw [ulit_toNat' _ (by have := hv.1.1; change _ < 2^256; omega)]
      exact fixedAllocation_next .bytes192 hh
    have hm1 := hm.preserve hc0.1 hn hnext
    have hm2 : CopyRequestArrayMemory final array rs (i+1) next := hm1.set hi hc0.2.1 hc0.2.2.2.1
      (le_of_eq hc0.2.2.2.2.1) hspan (by rw [hdp]; omega) hnext
    have hpre : MemoryPrefix mem final array.toNat := (hc0.1.mono (by omega)).trans
      (memoryPrefix_sparse_writeWord copied _ _ heap (Or.inl (by omega)))
    have hfree' : memLoad (UInt256.ofNat 64) final = UInt256.ofNat next :=
      (memLoad_write_below copied _ _ heap (by change 96 ≤ _; have := hm.low; omega)
        (by change 96 ≤ copied.size; have := hc0.2.2.2.2.2; omega)).trans hc0.2.2.1
    obtain ⟨a3,k3,C3,r3⟩ := easCopyRequestArraySet v (by simp only [List.length_cons]; omega) r2
    rw [hdst,wordStride32_next (array.toNat+32) i (by have := hv.2.2.1; change _ < 2^256; omega),
      wordStride32_next offset.toNat i (by change _ < 2^256; omega)] at r3
    exact Or.inl ⟨(allocateBlockLocals L next).insert "i" (.int (Int.ofNat (i+1))),final,a3,k3,C3,next,
      hn,hv.2.2.1,hpre,hf.next,hm2,hfree',hsol.1 hv,r3⟩
  · exact Or.inr ⟨hsol.2 hv,hrun.2 (fun h => hv (hg.mp h))⟩

theorem copyRequestArrayStep {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {offset array heap ret : UInt256} {rs : List AttestationRequestRecord} {i : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+23 ≤ 1024)
    (hf : CopyRequestArrayLocals L rs heap.toNat i) (hm : CopyRequestArrayMemory mem array rs i heap.toNat)
    (hc : RequestArrayCalldataView ee.calldata offset rs) (hi : i < rs.length)
    (hh : heap.toNat ≤ 2^64-1) (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (hsize : ee.calldata.size < 2^255+4)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5594⟩
      (UInt256.ofNat (array.toNat+32+32*i)::UInt256.ofNat (offset.toNat+32*i)::offset::
        UInt256.ofNat (offset.toNat+32*rs.length)::UInt256.ofNat ee.calldata.size::ret::array::R) mem aw rdata σ k C) :
    (∃ L' mem' aw' k' C' next,
      heap.toNat ≤ next ∧ next ≤ 2^64-1 ∧ MemoryPrefix mem mem' array.toNat ∧
      CopyRequestArrayLocals L' rs next (i+1) ∧ CopyRequestArrayMemory mem' array rs (i+1) next ∧
      memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat next ∧
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm copyRequestArrayIteration
        (.ok {contract := contract,locals := L',immutables := immStore v} evm) ∧
      RD fork (deployedRuntime v) ee g s0 ⟨5594⟩
        (UInt256.ofNat (array.toNat+32+32*(i+1))::UInt256.ofNat (offset.toNat+32*(i+1))::offset::
          UInt256.ofNat (offset.toNat+32*rs.length)::UInt256.ofNat ee.calldata.size::ret::array::R) mem' aw' rdata σ k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm copyRequestArrayIteration .reverted ∧
      RDrev fork (deployedRuntime v) g s0) :=
  copyRequestArrayStepOfElement v hstack hf hm hc.extent hi (hc.requests i hi) hh hfree hsize rd

end Benchmarks.EAS.EAS

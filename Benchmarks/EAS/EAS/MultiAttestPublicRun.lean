import Benchmarks.EAS.EAS.MultiAttestRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem multiAttestPublicRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+48 ≤ 1024) (hstate : SourceState s0 ee σ evm)
    (hvalid : wordArrayValid ee.calldata)
    (hreq : L.get? "multiRequests" = some (.array (multiRequestValues ee.calldata
      (UInt256.ofNat (wordArrayOffset ee.calldata+36)) (wordArrayLength ee.calldata))))
    (hheap : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat 224)))
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨3713⟩
      (UInt256.ofNat (wordArrayLength ee.calldata)::UInt256.ofNat (wordArrayOffset ee.calldata+36)::R)
      (Reasoning.Theory.writeWord ByteArray.empty 64 (UInt256.ofNat 224)) aw out σ k C) :
    (∃ (L' : Store) (evm' : EVM.State) (σ' : AccountMap) (words : List UInt256),
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiAttestAllocateBody++multiAttestTail)
        (.returned {contract := contract,locals := L',immutables := immStore v} evm' (some [wordListValue words])) ∧
      SourceState s0 ee σ' evm' ∧
      RDret fork (deployedRuntime v) g s0 σ' (wordBytes ([UInt256.ofNat 32,UInt256.ofNat words.length]++words))) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiAttestAllocateBody++multiAttestTail) .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiAttestAllocateBody++multiAttestTail) .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  let n := wordArrayLength ee.calldata
  let base := UInt256.ofNat (wordArrayOffset ee.calldata+36)
  let initial := Reasoning.Theory.writeWord ByteArray.empty 64 (UInt256.ofNat 224)
  let next := allocateNext 224 (32+32*n)
  have hn : n ≤ 2^64-1 := hvalid.2.2.2.1
  have hb : base.toNat = wordArrayOffset ee.calldata+36 := ulit_toNat' _
    (by have := hvalid.2.1; have := hvalid.2.2.1; change _ < 2^256; omega)
  have hbase : base.toNat+32*n < UInt256.size := by
    rw [hb]
    have := hvalid.2.1
    have he : wordArrayOffset ee.calldata+36+32*n ≤ ee.calldata.size := hvalid.2.2.2.2
    change _ < 2^256
    omega
  have ha := easMultiAttestAllocate (heap := UInt256.ofNat 224) v (by omega) hn (by decide) (by native_decide) rd
  simp only [show (UInt256.ofNat 224).toNat = 224 from rfl] at ha
  have hs := multiAttestAllocateSource (fork := fork) (imms := immStore v) (evm := evm) hreq hheap
    (by rw [multiRequestValues_length]; exact hn)
  dsimp only at hs
  rw [multiRequestValues_length,hstate.env] at hs
  by_cases hv : next ≤ 2^64-1 ∧ 224 ≤ next
  · rw [if_pos hv] at ha hs
    obtain ⟨a1,j1,D1,r1⟩ := ha
    obtain ⟨hsol1,hf1⟩ := hs
    have hnext : (UInt256.ofNat next).toNat = next := ulit_toNat' _ (by change next < 2^256; omega)
    have hmem := arrayTableAllocationMemory_view initial (UInt256.ofNat 224) n (by decide) (by decide) hn
    have hm : MultiAttestMemory (arrayTableAllocationMemory initial (UInt256.ofNat 224) n)
        (UInt256.ofNat 224) (List.replicate n []) 0 (UInt256.ofNat next).toNat := by
      rw [hnext]
      exact ⟨hmem.2.1,by decide,EmptyArraySuffix.replicate n,hmem.2.2,arrayTableAllocationMemory_zero96 n⟩
    have hstart : MultiAttestAt fork v ee g s0 n base (UInt256.ofNat 224) R 0
        (multiAttestInitialLocals L n next ee.weiValue) evm := by
      refine ⟨σ,_,out,a1,j1,D1,UInt256.ofNat next,ee.weiValue,List.replicate n [],hstate,
        by rw [hnext]; exact hv.1,by rw [List.length_replicate],?_,hm,?_⟩
      · rw [hnext]; exact hf1
      · simpa only [List.flatten_replicate_nil,List.length_nil] using r1
    rcases multiAttestRun v hstack hvalid.2.1 hbase hstart with
      ⟨L2,e2,σ2,words,hsol2,hs2,hret⟩ | ⟨hsol2,hrev⟩ | ⟨hsol2,hstatic⟩
    · exact Or.inl ⟨L2,e2,σ2,words,execBlock_append hsol1 hsol2,hs2,hret⟩
    · exact Or.inr (Or.inl ⟨execBlock_append hsol1 hsol2,hrev⟩)
    · exact Or.inr (Or.inr ⟨execBlock_append hsol1 hsol2,hstatic⟩)
  · rw [if_neg hv] at ha hs
    exact Or.inr (Or.inl ⟨execBlock_append_term hs (by intros; exact nofun),ha⟩)

end Benchmarks.EAS.EAS

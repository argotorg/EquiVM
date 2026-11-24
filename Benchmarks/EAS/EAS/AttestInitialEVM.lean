import Benchmarks.EAS.EAS.AttestAllocationMemory

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def attestInitialMemory (kind : AttestCallKind) (mem calldata : ByteArray) (heap data attester schema : UInt256) (len : Nat) : ByteArray :=
  attestUIDMemory (attestAllocationMemory kind mem heap data attester) calldata
    (UInt256.ofNat (allocateNext heap.toNat 64)) (UInt256.ofNat (allocateNext heap.toNat 128)) schema len

theorem easAttestInitial {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw schema data attester available last ret heap : UInt256}
    {σ : AccountMap} {k C len : Nat} {R : List UInt256}
    (v : EASImmutables) (kind : AttestCallKind) (hstack : R.length+20 ≤ 1024)
    (hlo : 224 ≤ data.toNat) (hspan : data.toNat+32 ≤ heap.toNat) (hcovered : data.toNat+32 ≤ mem.size)
    (hh : heap.toNat ≤ 2^64-1) (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩) (hlen : memLoad data mem = UInt256.ofNat len)
    (hlb : len < UInt256.size) (hcd : ee.calldata.size < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 kind.entryPC
      (attestEntryStack kind schema data attester available last ret R) mem aw rdata σ k C) :
    let first := allocateNext heap.toNat 128
    let next := allocateNext first (32+32*len)
    let ptr := UInt256.ofNat next
    let result := UInt256.ofNat (allocateNext heap.toNat 64)
    if first ≤ 2^64-1 ∧ heap.toNat ≤ first then
      if len ≤ 2^64-1 then
        if next ≤ 2^64-1 ∧ first ≤ next then
          ∃ gasArg aw' k' C', RD fork (deployedRuntime v) ee g s0
            (schemaCallPC (attestCallSchemaSite kind schema available last ret (UInt256.ofNat len)))
            (gasArg::UInt256.land (EVM.word v._schemaRegistry.val) solcAddrMask::ptr::⟨36⟩::ptr::⟨0⟩::
              schemaCallSaved (attestCallSchemaSite kind schema available last ret (UInt256.ofNat len)) ptr
                (attestCallSchemaSaved kind data attester available ret result R))
            (attestInitialMemory kind mem ee.calldata heap data attester schema len) aw' rdata σ k' C'
        else RDrev fork (deployedRuntime v) g s0
      else RDrev fork (deployedRuntime v) g s0
    else RDrev fork (deployedRuntime v) g s0 := by
  dsimp only
  obtain ⟨hsize0,hfree0,hzero0,hdata0,hregs0⟩ := attestEntryMemory_facts kind mem data attester heap (by omega) hlo hcovered hheap hzero
  obtain ⟨a1,k1,C1,r1⟩ := easAttestEntry v kind (by omega) rd
  have hr := easAttestResultAllocate v kind (by omega) hlo hspan (le_trans hcovered hsize0)
    hh hfree0 (hdata0.trans hlen) (fun hk => (hregs0 hk).2) r1
  by_cases hg : allocateNext heap.toNat 128 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 128
  · rw [if_pos hg] at hr ⊢
    obtain ⟨a2,k2,C2,r2⟩ := hr
    obtain ⟨a3,k3,C3,r3⟩ := easAttestUIDPrepare v kind (by omega) r2
    obtain ⟨hsize,hrlo,hrspan,huidcover,hfree,hzero,hused,hregs⟩ :=
      attestAllocationMemory_facts kind mem heap data attester (by omega) hlo hcovered hspan hh hheap hzero hg.1
    have hu : (UInt256.ofNat (allocateNext heap.toNat 128)).toNat = allocateNext heap.toNat 128 :=
      ulit_toNat' _ (by change _ < 2^256; omega)
    have ha := easWordArrayAllocate v
      (by cases kind <;> simp only [attestUIDSaved,List.length_cons] <;> omega)
      (by rw [hu]; exact hg.1) hfree hcd
      (by cases kind <;> simp only [AttestCallKind.uidReturn] <;> rw [easPatchedValidJumps v] <;> jump_dest) r3
    rw [ulit_toNat' _ hlb,hu] at ha
    by_cases hl : len ≤ 2^64-1
    · rw [if_pos hl] at ha ⊢
      split at ha
      · rename_i hn
        rw [if_pos hn]
        obtain ⟨a4,k4,C4,r4⟩ := ha
        obtain ⟨hp,hcover,hlen',hfree',hview⟩ := wordArrayAllocationMemory_view
          (attestAllocationMemory kind mem heap data attester) ee.calldata
          (UInt256.ofNat (allocateNext heap.toNat 128)) len (by rw [hu]; omega) (by rw [hu]; exact hg.1) hl
        have hn' : (UInt256.ofNat (allocateNext (allocateNext heap.toNat 128) (32+32*len))).toNat =
            allocateNext (allocateNext heap.toNat 128) (32+32*len) := ulit_toNat' _ (by change _ < 2^256; omega)
        rw [hu] at hp hcover hfree' hview
        have hregs' : kind = .many → memLoad (UInt256.ofNat 128)
            (wordArrayAllocationMemory (attestAllocationMemory kind mem heap data attester) ee.calldata
              (UInt256.ofNat (allocateNext heap.toNat 128)) len) = UInt256.ofNat (allocateNext heap.toNat 64) := by
          intro hk
          exact (memLoad_of_prefix hp (UInt256.ofNat 128) (by decide) (by change 160 ≤ _; omega)
            (by change 160 ≤ _; omega)).trans (hregs hk).1
        have hs := easAttestSchemaPrepare v kind (by omega) (by omega)
          (by rw [hn']; rw [hu] at hrspan; omega) (by rw [hn']; exact hn.1)
          (by have := hp.size; change 96 ≤ _; omega) hfree' hregs' r4
        simpa only [attestInitialMemory,attestUIDMemory,hu] using hs
      · rename_i hn
        simpa only [if_neg hn] using ha
    · simpa only [if_neg hl] using ha
  · simpa only [if_neg hg] using hr

end Benchmarks.EAS.EAS

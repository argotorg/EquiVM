import Benchmarks.EAS.EAS.RevokeArraysControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easRevokeArrays {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables) (site : RevokeSite) (hstack : R.length+22 ≤ 1024)
    (hlo : 96 ≤ site.records.toNat) (hh : site.records.toNat ≤ 2^64-1)
    (hlen : site.length < UInt256.size) (hl : memLoad site.data mem = UInt256.ofNat site.length)
    (hheap : memLoad (UInt256.ofNat 64) mem = site.records) (hcd : ee.calldata.size < UInt256.size)
    (hv : site.values = UInt256.ofNat (allocateNext site.records.toNat (32+352*site.length)))
    (rd : RD fork (deployedRuntime v) ee g s0 site.kind.arraysPC (revokeArraysStack site R) mem aw rdata σ k C) :
    let middle := allocateNext site.records.toNat (32+352*site.length)
    let next := allocateNext middle (32+32*site.length)
    if site.length ≤ 2^64-1 then
      if middle ≤ 2^64-1 ∧ site.records.toNat ≤ middle then
        if next ≤ 2^64-1 ∧ middle ≤ next then
          ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 site.kind.loopPC
            (revokeLoopStack site ee ⟨0⟩ R) (attestArraysMemory mem ee.calldata site.records site.length) aw' rdata σ k' C'
        else RDrev fork (deployedRuntime v) g s0
      else RDrev fork (deployedRuntime v) g s0
    else RDrev fork (deployedRuntime v) g s0 := by
  dsimp only
  obtain ⟨a1,k1,C1,r1⟩ := easRevokeRecordsStart v site (by omega) hl rd
  have hrecords := easDefaultArrayAllocate v
    (by cases hk : site.kind <;> simp only [revokeRecordsSaved,hk,List.length_append,List.length_cons,List.length_nil] <;> omega)
    hlo hh hheap
    (by rw [easPatchedValidJumps v]; cases site.kind <;> simp only [RevokeKind.recordsReturnPC] <;> jump_dest) r1
  rw [ulit_toNat' site.length hlen] at hrecords
  by_cases hlen64 : site.length ≤ 2^64-1
  · rw [if_pos hlen64] at hrecords ⊢
    by_cases hg : allocateNext site.records.toNat (32+352*site.length) ≤ 2^64-1 ∧
        site.records.toNat ≤ allocateNext site.records.toNat (32+352*site.length)
    · rw [if_pos hg] at hrecords ⊢
      obtain ⟨a2,k2,C2,r2⟩ := hrecords
      obtain ⟨a3,k3,C3,r3⟩ := easRevokeValuesStart v site (by omega) r2
      have hm := defaultArrayMemory_view mem site.records site.length hlo hh hlen64
      have hn : (UInt256.ofNat (allocateNext site.records.toNat (32+352*site.length))).toNat =
          allocateNext site.records.toNat (32+352*site.length) := ulit_toNat' _ (by change _ < 2^256; omega)
      have hvalues := easWordArrayAllocate v
        (by cases hk : site.kind <;> simp only [revokeValuesSaved,hk,List.length_append,List.length_cons,List.length_nil] <;> omega)
        (by rw [hn]; exact hg.1) hm.2.2.1 hcd
        (by rw [easPatchedValidJumps v]; cases site.kind <;> simp only [RevokeKind.valuesReturnPC] <;> jump_dest) r3
      rw [ulit_toNat' site.length hlen,if_pos hlen64,hn] at hvalues
      split at hvalues
      · rename_i hg2
        rw [if_pos hg2]
        obtain ⟨a4,k4,C4,r4⟩ := hvalues
        apply easRevokeArraysDone v site (by omega)
        simpa only [hv] using r4
      · rename_i hg2
        rw [if_neg hg2]
        exact hvalues
    · simpa only [if_neg hg] using hrecords
  · simpa only [if_neg hlen64] using hrecords

end Benchmarks.EAS.EAS

import Benchmarks.EAS.EAS.RequestTimeDispatch

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem easRequestTimeRun {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {cell schema idx t3 t4 expire : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+17 ≤ 1024) (hp : memLoad cell mem = refUIDPtr site t3)
    (he : UInt256.land (memLoad (refUIDPtr site t3+UInt256.ofNat 32) mem) easUint64Mask = expire)
    (rd : RD fork (deployedRuntime v) ee g s0 (requestTimePC site) (requestTimeStack site cell schema idx t3 t4 R) mem aw rdata σ k C) :
    if expire.toNat = 0 ∨ (easTimeWord ee).toNat < expire.toNat then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (requestRevocablePC site)
        (uidSaved site (refUIDPtr site t3+UInt256.ofNat 32) (schema::idx::t3::t4::R)) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  obtain ⟨aw1,k1,C1,h1⟩ := easRequestTimeDispatch v site hstack hp he rd
  have hb : (uidSaved site (refUIDPtr site t3+UInt256.ofNat 32) (schema::idx::t3::t4::R)).length+3 ≤ 1024 := by
    cases site <;> simp only [uidSaved,List.length_cons] <;> omega
  by_cases hz : expire = ⟨0⟩
  · rw [if_pos hz] at h1
    have hzero : expire.toNat = 0 := congrArg UInt256.toNat hz
    rw [if_pos (Or.inl hzero)]
    have h2 := easRequestTimeRequire v site (by omega) h1
    simpa only [hz,show UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256)) = ⟨0⟩ from by decide,if_pos rfl] using h2
  · rw [if_neg hz] at h1
    obtain ⟨aw2,k2,C2,h2⟩ := easRequestTimeCompare v site hb h1
    have h3 := easRequestTimeRequire v site (by omega) h2
    by_cases ht : (easTimeWord ee).toNat < expire.toNat
    · rw [if_pos (Or.inr ht)]
      simpa only [ult_one ht,show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide,if_pos rfl] using h3
    · rw [if_neg (by rintro (h | h); exact hz (uint256_toNat_eq_zero h); exact ht h)]
      simpa only [ult_zero (Nat.le_of_not_gt ht),show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide,
        if_neg (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)] using h3

end Benchmarks.EAS.EAS

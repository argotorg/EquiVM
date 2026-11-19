import Benchmarks.Midnight.Common

/-! Retaining cumulative gas payment through persistent writes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES Reasoning.Reach.RD.sstore by retaining the cumulative cost bound.
theorem sstoreMono {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : ℕ}
    {slot val : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (slot :: val :: t) mem aw rdata σ k C)
    (hperm : ee.perm = true)
    (hdec : decode code pc = some (.SSTORE, .none))
    (hov : t.length ≤ 1024) :
    ∃ k' C', C ≤ C' ∧ RD code ee g s0 (pc + ⟨1⟩) t mem aw rdata
      (sstoreAccountMap ee.codeOwner σ slot val) k' C' := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hσ₀⟩
  · exact ⟨k, C, le_rfl, Or.inl hoog⟩
  · have hperms : s.executionEnv.perm = true := by rw [hee]; exact hperm
    have st := sstore_xstep hcode hpc hdec hperms hstk hov
    have hmax : Csstore s ≤ max (Csstore s) (GasConstants.Gcallstipend + 1) := le_max_left _ _
    have hpos := Reasoning.Theory.Csstore_pos s
    by_cases gg : g.toNat < C + max (Csstore s) (GasConstants.Gcallstipend + 1)
    · exact ⟨k, C, le_rfl, Or.inl (hX.trans (stepOOG hgas st hk hC gg))⟩
    · have hcss : Csstore s ≤ s.machineState.gasAvailable.toNat := by simp [hgas, Sat256.subNat, Sat256.toNat]; rw [← Sat256.toNat]; omega
      refine ⟨k + 1, C + Csstore s, by omega, Or.inr ⟨stSStore s slot val t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)),
        ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [stSStore_executionEnv]; exact hcode
      · rw [stSStore_pc, hpc]
      · exact stSStore_stack s slot val t
      · rw [stSStore_gas s slot val t, ← Sat256.subNat_sub_add_of_sub_sub, hgas]
      · rw [stSStore_memory]; exact hmem
      · rw [stSStore_activeWords]; exact haw
      · exact hrdata
      · have hσ : s.accountMap = σ := hacc
        have hco : s.executionEnv.codeOwner = ee.codeOwner := by rw [hee]
        rw [stSStore_accountMap, hσ, hco]
      · rw [stSStore_executionEnv]; exact hee
      · exact hσ₀

end Benchmarks.Midnight

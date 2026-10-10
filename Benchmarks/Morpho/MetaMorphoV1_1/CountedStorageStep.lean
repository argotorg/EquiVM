import Reasoning.Reach

/-! A storage step retaining counters for proofs about loops that exhaust finite gas. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: strengthen RD.sstore with its exact step count and positive gas cost.
theorem rdSstoreCounted {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {slot value : UInt256} {R : List UInt256}
    (rd : RD code ee g s0 pc (slot :: value :: R) mem aw out σ k C)
    (hperm : ee.perm = true) (hdec : decode code pc = some (.SSTORE, none))
    (hstack : R.length ≤ 1024) :
    ∃ C', C + 1 ≤ C' ∧ RD code ee g s0 (pc + ⟨1⟩) R mem aw out
      (sstoreAccountMap ee.codeOwner σ slot value) (k + 1) C' := by
  rcases rd with hoog |
    ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hout, hacc, hee, hworld⟩
  · exact ⟨C + 1, le_rfl, Or.inl hoog⟩
  · have hp : s.executionEnv.perm = true := by rw [hee]; exact hperm
    have hs := sstore_xstep hcode hpc hdec hp hstk hstack
    have hmax := le_max_left (Csstore s) (GasConstants.Gcallstipend + 1)
    have hpos := Reasoning.Theory.Csstore_pos s
    by_cases hg : g.toNat < C + max (Csstore s) (GasConstants.Gcallstipend + 1)
    · exact ⟨C + 1, le_rfl, Or.inl (hX.trans (stepOOG hgas hs hk hC hg))⟩
    · refine ⟨C + Csstore s, by omega, Or.inr ⟨stSStore s slot value R,
        hX.trans (stepContinue hgas hs hk (Nat.not_lt.mp hg)),
        ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [stSStore_executionEnv]; exact hcode
      · rw [stSStore_pc, hpc]
      · exact stSStore_stack s slot value R
      · rw [stSStore_gas, ← Sat256.subNat_sub_add_of_sub_sub, hgas]
      · rw [stSStore_memory]; exact hmem
      · rw [stSStore_activeWords]; exact haw
      · exact hout
      · have howner : s.executionEnv.codeOwner = ee.codeOwner := by rw [hee]
        rw [stSStore_accountMap, hacc, howner]
      · rw [stSStore_executionEnv]; exact hee
      · exact hworld

end Benchmarks.Morpho.MetaMorphoV1_1

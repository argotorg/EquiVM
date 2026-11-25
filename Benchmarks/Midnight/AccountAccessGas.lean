import Benchmarks.Midnight.Common

variable {fork : Ethereum.Fork}

/-! Monotone parent charges for account-access opcodes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES Reasoning.Reach.RD.extcodesize by retaining the cumulative cost bound.
theorem extcodesizeMono {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : ℕ}
    {target : UInt256} {t : List UInt256}
    (h : RD fork code ee g s0 pc (target :: t) mem aw rdata σ k C)
    (hdec : decode code pc = some (.EXTCODESIZE, .none)) (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', C ≤ C' ∧ RD fork code ee g s0 (pc + ⟨1⟩)
      (extCodeSizeWord σ target :: t) mem aw rdata σ k' C' := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee,
    hσ₀⟩
  · exact ⟨k, C, le_rfl, Or.inl hoog⟩
  · have st := extcodesize_xstep (fork := fork) hcode hpc hdec hstk hov
    have hσ : s.accountMap = σ := hacc
    by_cases gg : g.toNat < C + Caccess (AccountAddress.ofUInt256 target) s.substate
    · exact ⟨k, C, le_rfl, Or.inl (hX.trans (stepOOG hgas st hk hC gg))⟩
    · refine ⟨k + 1, C + Caccess (AccountAddress.ofUInt256 target) s.substate, by omega,
        Or.inr ⟨stExtcodesize s target t,
          hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
          by
            have hpos : 1 ≤ Caccess (AccountAddress.ofUInt256 target) s.substate := by
              unfold Caccess; split <;> decide
            omega,
          by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · simp only [stExtcodesize]; exact hcode
      · simp only [stExtcodesize]; rw [hpc]
      · simp only [stExtcodesize, extCodeSizeWord, hσ]
      · simp only [stExtcodesize]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stExtcodesize]; exact hmem
      · simp only [stExtcodesize]; exact haw
      · simp only [stExtcodesize]; exact hrdata
      · simp only [stExtcodesize]; rw [hσ]
      · simp only [stExtcodesize]; exact hee
      · exact hσ₀

end Benchmarks.Midnight

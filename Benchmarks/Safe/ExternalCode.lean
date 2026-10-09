import Benchmarks.Safe.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def externalCode (σ : AccountMap) (target : UInt256) : ByteArray :=
  σ.get? (AccountAddress.ofUInt256 target) |>.option .empty (·.code)

def stExtcodecopy (s : State) (target dest source len : UInt256) (t : List UInt256) : State :=
  { s with
    substate.accessedAccounts := s.substate.accessedAccounts.insert (AccountAddress.ofUInt256
      target)
    machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩
      stack := t
      memory := (externalCode s.accountMap target).write source.toNat
        s.machineState.memory dest.toNat len.toNat
      activeWords := M s.machineState.activeWords dest len
      execLength := s.machineState.execLength + 1
      gasAvailable := (s.machineState.gasAvailable.subNat (memoryExpansionCost s
        .EXTCODECOPY)).subNat
        (Caccess (AccountAddress.ofUInt256 target) s.substate +
          GasConstants.Gcopy * ((len.toNat + 31) / 32)) } }

-- LIBRARY CANDIDATE: EXTCODECOPY, including both stages of its gas charge.
theorem extcodecopy_xstep {s : State} {code : ByteArray} {pc target dest source len : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pc)
    (hdec : decode code pc = some (.EXTCODECOPY, .none))
    (hstk : s.machineState.stack = target :: dest :: source :: len :: t)
    (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < memoryExpansionCost s .EXTCODECOPY
       then .error .OutOfGass
       else if (s.machineState.gasAvailable.subNat (memoryExpansionCost s .EXTCODECOPY)).toNat <
          Caccess (AccountAddress.ofUInt256 target) s.substate +
            GasConstants.Gcopy * ((len.toNat + 31) / 32)
         then .error .OutOfGass
         else .ok (stExtcodecopy s target dest source len t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.EXTCODECOPY, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_extcodecopy s hd, hstk]
  have hov' : ¬ ((target :: dest :: source :: len :: t).length - 4 + 0 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', stExtcodecopy, externalCode, M]

-- LIBRARY CANDIDATE: an EXTCODECOPY reachability rule with an arbitrary account map.
theorem rdExtcodecopy {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : ℕ} {target dest source len : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (target :: dest :: source :: len :: t) mem aw rdata σ k C)
    (hdec : decode code pc = some (.EXTCODECOPY, .none)) (hov : t.length ≤ 1024) :
    ∃ k' C', RD code ee g s0 (pc + ⟨1⟩) t
      ((externalCode σ target).write source.toNat mem dest.toNat len.toNat)
      (M aw dest len) rdata σ k' C' := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hσ₀⟩
  · exact ⟨k, C, Or.inl hoog⟩
  · have hmc : memoryExpansionCost s .EXTCODECOPY = memExpansionCost aw dest len := by
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ, memExpansionCost, M]
    have st := extcodecopy_xstep hcode hpc hdec hstk hov
    rw [hmc, collapse_two_stage] at st
    let cost := memExpansionCost aw dest len +
      (Caccess (AccountAddress.ofUInt256 target) s.substate +
        GasConstants.Gcopy * ((len.toNat + 31) / 32))
    by_cases gg : g.toNat < C + cost
    · exact ⟨k, C, Or.inl (hX.trans (stepOOG hgas st hk hC gg))⟩
    · have hpos : 0 < cost := by
        have ha : 1 ≤ Caccess (AccountAddress.ofUInt256 target) s.substate := by
          unfold Caccess; split <;> decide
        dsimp [cost]; omega
      refine ⟨k + 1, C + cost, Or.inr ⟨stExtcodecopy s target dest source len t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
        by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · exact hcode
      · simp only [stExtcodecopy, hpc]
      · rfl
      · simp only [stExtcodecopy, hmc, hgas, Sat256.subNat_sub_add_of_sub_sub,
          cost, Nat.add_assoc]
      · simp only [stExtcodecopy, hacc, hmem]
      · simp only [stExtcodecopy, haw]
      · exact hrdata
      · exact hacc
      · exact hee
      · exact hσ₀

end Benchmarks.Safe

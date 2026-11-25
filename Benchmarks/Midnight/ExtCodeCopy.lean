import Benchmarks.Midnight.CodeStorage

variable {fork : Ethereum.Fork}

/-! The EXTCODECOPY boundary in code-storage readers. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES Reasoning.Reach.RD.genCodecopy: external code and warm/cold access cost.
def stExtCodeCopy (s : State) (target dst src len : UInt256) (tail : List UInt256) : State :=
  { s with
    substate := { s.substate with
      accessedAccounts := s.substate.accessedAccounts.insert (AccountAddress.ofUInt256 target) }
    machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩
      stack := tail
      memory := (externalCode s.accountMap target).write src.toNat s.machineState.memory dst.toNat len.toNat
      activeWords := M s.machineState.activeWords dst len
      execLength := s.machineState.execLength + 1
      gasAvailable := (s.machineState.gasAvailable.subNat (memoryExpansionCost s .EXTCODECOPY)).subNat
        (Caccess (AccountAddress.ofUInt256 target) s.substate +
          GasConstants.Gcopy * ((len.toNat + 31) / 32)) } }

theorem extCodeCopy_xstep {s : State} {code : ByteArray} {pc target dst src len : UInt256}
    {tail : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pc)
    (hdec : decode code pc = some (.EXTCODECOPY, .none))
    (hstack : s.machineState.stack = target :: dst :: src :: len :: tail)
    (hov : tail.length ≤ 1024) :
    Xstep fork (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < memoryExpansionCost s .EXTCODECOPY then
        .error .OutOfGass
      else if (s.machineState.gasAvailable.subNat (memoryExpansionCost s .EXTCODECOPY)).toNat <
          Caccess (AccountAddress.ofUInt256 target) s.substate +
            GasConstants.Gcopy * ((len.toNat + 31) / 32) then .error .OutOfGass
      else .ok (stExtCodeCopy s target dst src len tail, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.EXTCODECOPY, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_extcodecopy s hd, hstack]
  have hlen : ¬ (target :: dst :: src :: len :: tail).length - 4 + 0 > 1024 := by
    simp only [List.length_cons]; omega
  simp only [if_neg hlen, stExtCodeCopy, externalCode, M]

theorem extCodeCopyReach {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc target dst src len : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {accounts : AccountMap} {k C : Nat}
    (h : RD fork code ee g s0 pc (target :: dst :: src :: len :: tail) mem aw rdata accounts k C)
    (hdec : decode code pc = some (.EXTCODECOPY, .none)) (hov : tail.length ≤ 1024) :
    ∃ k' C', RD fork code ee g s0 (pc + ⟨1⟩) tail
      ((externalCode accounts target).write src.toNat mem dst.toNat len.toNat)
      (M aw dst len) rdata accounts k' C' := by
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstack, hgas, hk, hC,
    hmem, haw, hrdata, hacc, hee, hσ₀⟩
  · exact ⟨k, C, Or.inl hoog⟩
  have hmc : memoryExpansionCost s .EXTCODECOPY = memExpansionCost aw dst len := by
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstack,
      List.getElem!_cons_zero, List.getElem!_cons_succ, M, memExpansionCost]
  have st := extCodeCopy_xstep (fork := fork) hcode hpc hdec hstack hov
  rw [hmc, collapse_two_stage] at st
  let cost := memExpansionCost aw dst len +
    (Caccess (AccountAddress.ofUInt256 target) s.substate +
      GasConstants.Gcopy * ((len.toNat + 31) / 32))
  by_cases gg : g.toNat < C + cost
  · exact ⟨k, C, Or.inl (hX.trans (stepOOG hgas st hk hC gg))⟩
  have hpos : 0 < cost := by
    have ha : 0 < Caccess (AccountAddress.ofUInt256 target) s.substate := by
      unfold Caccess; split <;> decide
    dsimp [cost]; omega
  refine ⟨k + 1, C + cost, Or.inr ⟨stExtCodeCopy s target dst src len tail,
    hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, rfl, ?_, by omega,
    by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact hcode
  · simp only [stExtCodeCopy, hpc]
  · simp only [stExtCodeCopy, hmc, hgas, cost,
      Sat256.subNat_sub_add_of_sub_sub, Nat.add_assoc]
  · simp only [stExtCodeCopy, hmem, hacc]
  · simp only [stExtCodeCopy, haw]
  · exact hrdata
  · exact hacc
  · exact hee
  · exact hσ₀

end Benchmarks.Midnight

import Benchmarks.Auction.DynamicMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- GENERALIZES Reasoning.Theory.stLog1/log1_xstep to the missing two-topic instruction.
def stLog2 (s : State) (a b c d : UInt256) (t : List UInt256) : State :=
  { s with
    substate.logSeries := s.substate.logSeries.push
      ⟨s.executionEnv.codeOwner, #[c, d], s.machineState.memory.readWithPadding a.toNat b.toNat⟩
    machineState.stack := t
    machineState.activeWords :=
      UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
    machineState.gasAvailable :=
      (s.machineState.gasAvailable.subNat (memoryExpansionCost s .LOG2)).subNat
        (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic)
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1 }

theorem log2_xstep {s : State} {code : ByteArray} {pcv a b c d : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.LOG2, .none)) (hperm : s.executionEnv.perm = true)
    (hstk : s.machineState.stack = a :: b :: c :: d :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < memoryExpansionCost s .LOG2 +
          (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic)
       then .error .OutOfGass else .ok (stLog2 s a b c d t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.LOG2, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_log2 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: t).length - 4 + 0 > 1024) := by
    simp only [List.length_cons]; omega
  have hpermF : (¬ s.executionEnv.perm = true) = False := eq_false (by simp [hperm])
  simp only [collapse_two_stage, if_neg hov', hpermF, if_false, stLog2]

end Auction

namespace Reasoning.Reach

open Auction

-- GENERALIZES Reasoning.Reach.RD.log1 to two topics, with symbolic expansion and exact gas.
theorem RD.log2Symbolic {code I g s0 pc offset size topic1 topic2 R mem aw rdata acc k C}
    (h : RD code I g s0 pc (offset :: size :: topic1 :: topic2 :: R) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG2, .none)) (hperm : I.perm = true)
    (hov : R.length ≤ 1024) :
    ∃ k' C', RD code I g s0 (pc + ⟨1⟩) R mem (expandedWords aw offset size) rdata acc k' C' := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata,
    hacc, hee, hworld⟩
  · exact ⟨k, C, Or.inl hoog⟩
  · have hmc : memoryExpansionCost s .LOG2 = expansionCost aw offset size := by
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      rfl
    have hp : s.executionEnv.perm = true := by rw [hee]; exact hperm
    have st := log2_xstep hcode hpc hdec hp hstk hov
    rw [hmc] at st
    let cost := expansionCost aw offset size +
      (GasConstants.Glog + GasConstants.Glogdata * size.toNat + 2 * GasConstants.Glogtopic)
    by_cases gg : g.toNat < C + cost
    · exact ⟨k, C, Or.inl (hX.trans (stepOOG hgas st hk hC gg))⟩
    · refine ⟨k + 1, C + cost, Or.inr ⟨stLog2 s offset size topic1 topic2 R,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), hcode, ?_, rfl, ?_, ?_,
        Nat.not_lt.mp gg, hmem, ?_, hrdata, hacc, hee, hworld⟩⟩
      · simp only [stLog2]; rw [hpc]
      · simp only [stLog2, hmc, cost]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · have hlog : 1 ≤ GasConstants.Glog := by decide
        dsimp only [cost]
        omega
      · simp only [stLog2, expandedWords, haw]

end Reasoning.Reach

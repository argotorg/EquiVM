import Benchmarks.Auction.DynamicMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

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

import Benchmarks.Auction.DynamicMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Reach

open Auction

-- LIBRARY CANDIDATE: symbolic RETURNDATACOPY with its exact expansion and copy costs.
theorem RD.returndatacopySymbolic {code I g s0 pc dest src size R mem aw rdata acc k C}
    (h : RD code I g s0 pc (dest :: src :: size :: R) mem aw rdata acc k C)
    (hdec : decode code pc = some (.RETURNDATACOPY, .none))
    (hguard : src.toNat + size.toNat ≤ rdata.size) (hov : R.length ≤ 1024) :
    ∃ k' C', RD code I g s0 (pc + ⟨1⟩) R
      (rdata.write src.toNat mem dest.toNat size.toNat) (expandedWords aw dest size)
      rdata acc k' C' := by
  refine ⟨_, _, h.returndatacopy (expansionCost aw dest size) _ _ hdec hguard ?_ rfl rfl hov⟩
  intro s haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
  rfl

end Reasoning.Reach

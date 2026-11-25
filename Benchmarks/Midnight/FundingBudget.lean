import Benchmarks.Midnight.TransferBudget

/-! Retain unconditional memory funding through routines parameterized by a transfer budget. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def fundingBudgetRoot : UInt256 := UInt256.ofNat (2^64)

-- LIBRARY CANDIDATE: an aligned large sentinel makes the budget's small-heap alternative impossible.
theorem MemoryFunding.budget {credit mem aw spent} (h : MemoryFunding credit mem aw spent) :
    TransferBudget fundingBudgetRoot credit mem aw spent :=
  Or.inr ⟨by decide +kernel, h⟩

theorem TransferBudget.funding {credit mem aw spent}
    (h : TransferBudget fundingBudgetRoot credit mem aw spent) : MemoryFunding credit mem aw spent := by
  rcases h with hsmall | ⟨_, hfund⟩
  · exact False.elim ((by decide +kernel : ¬ fundingBudgetRoot.toNat + 160 ≤ 2^62) hsmall)
  · exact hfund

end Benchmarks.Midnight

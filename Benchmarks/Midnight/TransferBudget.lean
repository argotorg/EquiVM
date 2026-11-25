import Benchmarks.Midnight.MemoryFunding

variable {fork : Ethereum.Fork}

/-! Either a small transfer heap or the gas credit needed for a large heap. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def TransferBudget (root : UInt256) (credit : Nat) (mem : ByteArray) (aw : UInt256)
    (spent : Nat) : Prop :=
  root.toNat + 160 ≤ 2^62 ∨ (root.toNat % 32 = 0 ∧ MemoryFunding credit mem aw spent)

theorem TransferBudget.mono {root credit mem aw spent spent'}
    (h : TransferBudget root credit mem aw spent) (hle : spent ≤ spent') :
    TransferBudget root credit mem aw spent' :=
  h.imp_right (fun ⟨halign, hf⟩ ↦ ⟨halign, hf.mono hle⟩)

theorem transferBudgetAt {root credit code I g s0 pc stk mem aw rdata σ k C}
    (_rd : RD fork code I g s0 pc stk mem aw rdata σ k C)
    (h : TransferBudget root credit mem aw C) : TransferBudget root credit mem aw C := h

macro "transfer_budget" h:ident : tactic => `(tactic|
  (have hbudget := $h
   rcases hbudget with hsmall | ⟨halign, hfund⟩
   · exact Or.inl hsmall
   · refine Or.inr ⟨halign, ?_⟩
     memory_fund hfund))

end Benchmarks.Midnight

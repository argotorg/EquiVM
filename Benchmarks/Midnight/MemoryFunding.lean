import Benchmarks.Midnight.MemoryAccounting

/-! Memory payment with a retained lower bound on non-memory work. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

structure MemoryFunding (credit : Nat) (mem : ByteArray) (aw : UInt256) (spent : Nat) : Prop where
  paid : Cₘ aw + credit ≤ spent + 79
  covered : MemoryCovered mem aw

theorem MemoryFunding.accounting {credit mem aw spent} (h : MemoryFunding credit mem aw spent) :
    MemoryAccounting mem aw spent := by
  refine ⟨?_, h.covered⟩
  have hp := h.paid
  unfold MemoryPaid
  omega

theorem MemoryFunding.of_accounting {mem aw spent} (h : MemoryAccounting mem aw spent) :
    MemoryFunding 0 mem aw spent := by
  exact ⟨by simpa only [Nat.add_zero] using h.paid, h.covered⟩

theorem MemoryFunding.weaken {credit credit' mem aw spent}
    (h : MemoryFunding credit mem aw spent) (hle : credit' ≤ credit) :
    MemoryFunding credit' mem aw spent := by
  refine ⟨?_, h.covered⟩
  have hp := h.paid
  omega

theorem MemoryFunding.mono {credit mem aw spent spent'}
    (h : MemoryFunding credit mem aw spent) (hle : spent ≤ spent') :
    MemoryFunding credit mem aw spent' :=
  ⟨h.paid.trans (Nat.add_le_add_right hle 79), h.covered⟩

theorem memoryFundingAt {credit code I g s0 pc stk mem aw rdata σ k C}
    (_rd : RD code I g s0 pc stk mem aw rdata σ k C)
    (h : MemoryFunding credit mem aw C) : MemoryFunding credit mem aw C := h

macro "memory_fund" h:ident : tactic => `(tactic|
  (constructor
   · have hp := MemoryFunding.paid $h
     simp only [memExpansionCost, mcopyExpansionCost] at hp ⊢
     omega
   · have hc := MemoryFunding.covered $h
     memory_covered))

end Benchmarks.Midnight

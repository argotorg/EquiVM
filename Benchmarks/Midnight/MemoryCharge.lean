import Benchmarks.Midnight.MemoryFunding

variable {fork : Ethereum.Fork}

/-! Memory growth and non-memory gas charges across a runtime segment. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: compose gas charges without fixing a memory buffer or its contents.
structure MemoryCharge (work : Nat) (aw aw' : UInt256) (spent spent' : Nat) : Prop where
  work_le : spent + work ≤ spent'
  active_le : aw.toNat ≤ aw'.toNat
  paid : Cₘ aw' + spent + work ≤ Cₘ aw + spent'

theorem MemoryCharge.refl (aw : UInt256) (spent : Nat) : MemoryCharge 0 aw aw spent spent :=
  ⟨by omega, le_rfl, by omega⟩

theorem MemoryCharge.trans {work work' aw aw' aw'' spent spent' spent''}
    (h : MemoryCharge work aw aw' spent spent')
    (h' : MemoryCharge work' aw' aw'' spent' spent'') :
    MemoryCharge (work + work') aw aw'' spent spent'' := by
  exact ⟨by have := h.work_le; have := h'.work_le; omega,
    h.active_le.trans h'.active_le, by have := h.paid; have := h'.paid; omega⟩

theorem MemoryCharge.funding {work credit mem mem' aw aw' spent spent'}
    (h : MemoryCharge work aw aw' spent spent') (ha : MemoryFunding credit mem aw spent)
    (hc : MemoryCovered mem' aw') : MemoryFunding (credit + work) mem' aw' spent' := by
  exact ⟨by have := h.paid; have := ha.paid; omega, hc⟩

theorem MemoryCovered.mono {mem aw aw'} (h : MemoryCovered mem aw)
    (ha : aw.toNat ≤ aw'.toNat) : MemoryCovered mem aw' := by
  unfold MemoryCovered at *
  omega

theorem memoryChargeAt {work aw₀ C₀ code I g s0 pc stk mem aw rdata σ k C}
    (_rd : RD fork code I g s0 pc stk mem aw rdata σ k C)
    (h : MemoryCharge work aw₀ aw C₀ C) : MemoryCharge work aw₀ aw C₀ C := h

syntax "memory_expands" : tactic
macro_rules
| `(tactic| memory_expands) => `(tactic|
  first
  | assumption
  | exact le_rfl
  | (refine Nat.le_trans ?_ (memoryWords_ge _ _ _); memory_expands))

macro "memory_charge" h:ident : tactic => `(tactic|
  (constructor
   · have hw := MemoryCharge.work_le $h
     omega
   · have hm := MemoryCharge.active_le $h
     memory_expands
   · have hp := MemoryCharge.paid $h
     simp only [memExpansionCost, mcopyExpansionCost] at hp ⊢
     omega))

end Benchmarks.Midnight

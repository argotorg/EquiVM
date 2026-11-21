import Benchmarks.Midnight.GasMemory
import Benchmarks.Midnight.Conditions

/-! Explicit memory-payment facts to retain alongside reachability summaries. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def MemoryPaid (allowance : Nat) (aw : UInt256) (spent : Nat) : Prop :=
  Cₘ aw ≤ spent + allowance

theorem MemoryPaid.mono {allowance spent spent' : Nat} {aw : UInt256}
    (h : MemoryPaid allowance aw spent) (hle : spent ≤ spent') :
    MemoryPaid allowance aw spent' := by
  unfold MemoryPaid at *
  omega

theorem MemoryPaid.expand {allowance spent : Nat} {aw : UInt256} (off len : UInt256)
    (h : MemoryPaid allowance aw spent) :
    MemoryPaid allowance (M aw off len) (spent + memExpansionCost aw off len) := by
  unfold MemoryPaid memExpansionCost at *
  omega

theorem MemoryPaid.copy {allowance spent : Nat} {aw : UInt256} (dst src len : UInt256)
    (h : MemoryPaid allowance aw spent) :
    MemoryPaid allowance (Mmcopy aw dst src len) (spent + mcopyExpansionCost aw dst src len) := by
  unfold MemoryPaid mcopyExpansionCost at *
  omega

theorem MemoryPaid.entry (spent : Nat) : MemoryPaid 79 (UInt256.ofNat 26) spent := by
  have hc : Cₘ (UInt256.ofNat 26) = 79 := by decide +kernel
  unfold MemoryPaid
  rw [hc]
  omega

theorem memoryPaid_gasBound {code I g s0 pc stk mem aw rdata σ k C allowance}
    (rd : RD code I g s0 pc stk mem aw rdata σ k C) (hp : MemoryPaid allowance aw C) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨
      memoryCost aw.toNat ≤ g.toNat + allowance := by
  rcases rd with hoog | ⟨s, _, _, _, _, _, _, hC, _⟩
  · exact Or.inl hoog
  · have he : memoryCost aw.toNat = Cₘ aw := by
      rw [memoryCost_eq_Cₘ (words := aw.toNat) aw.val.isLt, u256_ofNat_toNat]
    exact Or.inr (by rw [he]; unfold MemoryPaid at hp; omega)

theorem midnightMemoryPaid_bound {code I g s0 pc stk mem aw rdata σ k C}
    (rd : RD code I g s0 pc stk mem aw rdata σ k C) (hp : MemoryPaid 79 aw C)
    (hgas : midnightGasBound g.toUInt256) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨ aw.toNat < 3 * 2^57 := by
  rcases memoryPaid_gasBound rd hp with hoog | hcost
  · exact Or.inl hoog
  · right
    by_contra hlarge
    have hlo := memoryCost_mono (show 3 * 2^57 ≤ aw.toNat by omega)
    have hthreshold : 327073817860464196263953616796569 + 79 < memoryCost (3 * 2^57) :=
      by decide +kernel
    have hgas' := midnightGasBound_lt_capacityCutoff hgas
    change g.toNat < 327073817860464196263953616796569 at hgas'
    omega

theorem midnightMemoryPaid_small {code I g s0 pc stk mem aw rdata σ k C}
    (rd : RD code I g s0 pc stk mem aw rdata σ k C) (hp : MemoryPaid 79 aw C)
    (hgas : midnightGasBound g.toUInt256) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨ aw.toNat < 100000 := by
  rcases memoryPaid_gasBound rd hp with hoog | hcost
  · exact Or.inl hoog
  · right
    by_contra hlarge
    have hlo := memoryCost_mono (show 100000 ≤ aw.toNat by omega)
    have hthreshold : 2^24 + 79 < memoryCost 100000 := by decide +kernel
    change g.toNat ≤ 2^24 at hgas
    omega

theorem midnightMemoryPaid_headroom {code I g s0 pc stk mem aw rdata σ k C}
    {root : UInt256}
    (rd : RD code I g s0 pc stk mem aw rdata σ k C) (hp : MemoryPaid 79 aw C)
    (hgas : midnightGasBound g.toUInt256) (hroot : root.toNat ≤ 32 * aw.toNat) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨ root.toNat + 2^62 < 2^64 := by
  rcases midnightMemoryPaid_bound rd hp hgas with hoog | haw
  · exact Or.inl hoog
  · exact Or.inr (by omega)

end Benchmarks.Midnight

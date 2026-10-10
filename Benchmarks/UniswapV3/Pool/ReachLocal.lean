import Benchmarks.UniswapV3.Pool.ReachFuel

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: restart a reached cursor with its remaining gas and zero local cost.
theorem rdLocalize {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {pc aw : UInt256} {stack : List UInt256} {mem rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} (rd : RD code ee g s0 pc stack mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨
      ∃ s : EVM.State, s.σ₀ = s0.σ₀ ∧ C ≤ g.toNat ∧
        X (g.toNat + 1) (D_J code 0) s0 = X ((g.subNat C).toNat + 1) (D_J code 0) s ∧
        RD code ee (g.subNat C) s pc stack mem aw rdata σ 0 0 := by
  rcases rd with hoog | ⟨s, hx, hc, hp, hs, hg, hk, hC, hm, haw, hr, hσ, he, hworld⟩
  · exact Or.inl hoog
  · refine Or.inr ⟨s, hworld, hC, ?_, ?_⟩
    · apply hx.trans
      apply evmRun_fuel_eq <;> simp only [hg, Sat256.subNat_toNat] <;> omega
    · exact Or.inr ⟨s, by simp only [Nat.sub_zero], hc, hp, hs,
        by simpa only [Sat256.subNat_zero] using hg,
        Nat.le_refl 0, Nat.zero_le _, hm, haw, hr, hσ, he, rfl⟩

-- LIBRARY CANDIDATE: lift a local cursor while retaining its consumed-cost lower bound.
theorem rdGlobalize {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 s : EVM.State}
    {pc aw : UInt256} {stack : List UInt256} {mem rdata : ByteArray} {σ : AccountMap}
    {C k' C' : Nat} (hworld : s.σ₀ = s0.σ₀) (hC : C ≤ g.toNat)
    (hx : X (g.toNat + 1) (D_J code 0) s0 = X ((g.subNat C).toNat + 1) (D_J code 0) s)
    (rd : RD code ee (g.subNat C) s pc stack mem aw rdata σ k' C') :
    RD code ee g s0 pc stack mem aw rdata σ (C + k') (C + C') := by
  rcases rd with hoog | ⟨next, hx', hc, hp, hs, hg, hk, hC', hm, haw, hr, hσ, he, hworld'⟩
  · exact Or.inl (hx.trans hoog)
  · have hcost : C + C' ≤ g.toNat := by
      simp only [Sat256.subNat_toNat] at hC'
      omega
    have hfuel : g.toNat + 1 - (C + k') = (g.subNat C).toNat + 1 - k' := by
      simp only [Sat256.subNat_toNat]
      omega
    refine Or.inr ⟨next, ?_, hc, hp, hs, ?_, by omega, hcost,
      hm, haw, hr, hσ, he, hworld'.trans hworld⟩
    · rw [hfuel]
      exact hx.trans hx'
    · simpa only [Sat256.subNat_subNat] using hg

end Benchmarks.UniswapV3.Pool

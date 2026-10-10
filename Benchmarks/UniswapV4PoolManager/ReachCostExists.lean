import Benchmarks.UniswapV4PoolManager.ReachCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: retain a cost floor when a routine existentially chooses its output cursor.
theorem RD_retainCost_exists {α : Type} {code : ByteArray} {I J : ExecutionEnv}
    {g : Sat256} {s0 : State} {entry : Cursor} {next : α → Cursor} {facts : α → Prop} {k C : Nat}
    (routine : ∀ (budget : Sat256) (start : State),
      RDc code I budget start entry 0 0 →
      ∃ a kr Cr, facts a ∧ RDc code J budget start (next a) kr Cr)
    (h : RDc code I g s0 entry k C) :
    ∃ a kr Cr, facts a ∧ C ≤ Cr ∧ RDc code J g s0 (next a) kr Cr := by
  rcases h with hog | ⟨s, hrun, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hI, hσ⟩
  · obtain ⟨a, _, _, hf, _⟩ := routine g s0 (.inl hog)
    exact ⟨a, k, C, hf, Nat.le_refl _, .inl hog⟩
  have hs : RDc code I (g.subNat C) s entry 0 0 := by
    apply RD.startWith hcode hpc hstk
      (by rw [Sat256.subNat_zero]; exact hgas) (Nat.le_refl _) (Nat.zero_le _) (by rw [Nat.sub_zero])
      hmem haw hrdata hacc hI rfl
  obtain ⟨a, kr, Cr, hf, hr⟩ := routine (g.subNat C) s hs
  have hX : X (g.toNat+1) (D_J code 0) s0 = X ((g.subNat C).toNat+1) (D_J code 0) s := by
    apply hrun.trans
    apply X_fuel_eq_of_gas_lt
    · rw [hgas, Sat256.subNat_toNat]; omega
    · rw [hgas]; omega
  exact ⟨a, k+kr, C+Cr, hf, by omega, RD_liftRebased hk hC hσ hX hr⟩

end Benchmarks.UniswapV4PoolManager

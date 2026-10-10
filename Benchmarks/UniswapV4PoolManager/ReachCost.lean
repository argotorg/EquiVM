import Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: any two fuel allowances above the remaining gas give the same run.
theorem X_fuel_eq_of_gas_lt {a b : Nat} {vj : Array UInt256} {s : State}
    (ha : s.machineState.gasAvailable.toNat < a) (hb : s.machineState.gasAvailable.toNat < b) :
    X a vj s = X b vj s := by
  induction a generalizing b s with
  | zero => omega
  | succ a ih =>
    cases b with
    | zero => omega
    | succ b =>
      rw [X, X]
      cases hs : Xstep vj s with
      | error e => rfl
      | ok result =>
        rcases result with ⟨post, halted⟩
        cases halted with
        | none =>
          have hg := Xstep_gas_decreases_of_continues hs
          exact ih (by change post.machineState.gasAvailable.toNat < a; omega)
            (by change post.machineState.gasAvailable.toNat < b; omega)
        | some result =>
          rcases result with ⟨cause, out⟩
          cases cause <;> rfl

-- LIBRARY CANDIDATE: compose a routine proved with a fresh gas counter at an existing cursor.
theorem RD_liftRebased {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 s : State}
    {pc aw : UInt256} {stk : List UInt256} {mem rdata : ByteArray} {σ : AccountMap}
    {k C kr Cr : Nat} (hk : k ≤ C) (hC : C ≤ g.toNat) (hσ : s.σ₀ = s0.σ₀)
    (hX : X (g.toNat+1) (D_J code 0) s0 = X ((g.subNat C).toNat+1) (D_J code 0) s)
    (h : RD code I (g.subNat C) s pc stk mem aw rdata σ kr Cr) :
    RD code I g s0 pc stk mem aw rdata σ (k+kr) (C+Cr) := by
  rcases h with hog | ⟨post, hrun, hcode, hpc, hstk, hgas, hkr, hCr, hmem, haw, hrdata, hacc, hI, hσr⟩
  · exact .inl (hX.trans hog)
  have hgas' : post.machineState.gasAvailable = g.subNat (C+Cr) := by
    rw [hgas, Sat256.subNat_subNat]
  have hCr' : C+Cr ≤ g.toNat := by
    rw [Sat256.subNat_toNat] at hCr
    omega
  refine .inr ⟨post, hX.trans (hrun.trans ?_), hcode, hpc, hstk, hgas', by omega, hCr',
    hmem, haw, hrdata, hacc, hI, hσr.trans hσ⟩
  apply X_fuel_eq_of_gas_lt
  · rw [hgas, Sat256.subNat_toNat]
    omega
  · rw [hgas', Sat256.subNat_toNat]
    omega

-- LIBRARY CANDIDATE: retain the incoming cost floor when a routine's summary hides its counters.
theorem RD_retainCost {code : ByteArray} {I J : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc pc' aw aw' : UInt256} {stk stk' : List UInt256} {mem mem' rdata rdata' : ByteArray}
    {σ σ' : AccountMap} {k C : Nat}
    (routine : ∀ (budget : Sat256) (start : State),
      RD code I budget start pc stk mem aw rdata σ 0 0 →
      ∃ kr Cr, RD code J budget start pc' stk' mem' aw' rdata' σ' kr Cr)
    (h : RD code I g s0 pc stk mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD code J g s0 pc' stk' mem' aw' rdata' σ' k' C' := by
  rcases h with hog | ⟨s, hrun, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hI, hσ⟩
  · exact ⟨k, C, Nat.le_refl _, .inl hog⟩
  have hs : RD code I (g.subNat C) s pc stk mem aw rdata σ 0 0 := by
    apply RD.startWith hcode hpc hstk
      (by rw [Sat256.subNat_zero]; exact hgas) (Nat.le_refl _) (Nat.zero_le _) (by rw [Nat.sub_zero])
      hmem haw hrdata hacc hI rfl
  obtain ⟨kr, Cr, hr⟩ := routine (g.subNat C) s hs
  have hX : X (g.toNat+1) (D_J code 0) s0 = X ((g.subNat C).toNat+1) (D_J code 0) s := by
    apply hrun.trans
    apply X_fuel_eq_of_gas_lt
    · rw [hgas, Sat256.subNat_toNat]; omega
    · rw [hgas]; omega
  exact ⟨k+kr, C+Cr, by omega, RD_liftRebased hk hC hσ hX hr⟩

end Benchmarks.UniswapV4PoolManager

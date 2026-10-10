import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE (Reasoning/Stepping): enough fuel makes the iterator fuel-independent.
theorem X_eq_of_gas_lt_fuel {validJumps : Array UInt256} {s : State} {f f' : Nat}
    (hf : s.machineState.gasAvailable.toNat < f)
    (hf' : s.machineState.gasAvailable.toNat < f') :
    X f validJumps s = X f' validJumps s := by
  induction f generalizing s f' with
  | zero => omega
  | succ f ih =>
      cases f' with
      | zero => omega
      | succ f' =>
          cases hstep : Xstep validJumps s with
          | error e => simp only [X, hstep, bind, Except.bind]
          | ok next =>
              obtain ⟨s', ret⟩ := next
              cases ret with
              | none =>
                  have hg := Xstep_gas_decreases_of_continues hstep
                  simp only [X, hstep, bind, Except.bind]
                  exact ih (by simpa using (show s'.machineState.gasAvailable.toNat < f by omega))
                    (by simpa using (show s'.machineState.gasAvailable.toNat < f' by omega))
              | some ret =>
                  obtain ⟨halt, out⟩ := ret
                  cases halt <;> simp only [X, hstep, bind, Except.bind]

-- LIBRARY CANDIDATE (Reasoning/Reach): run a helper on the remaining gas, then add its cost.
structure RunRemainder (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (C : Nat) (s : State) : Prop where
  cost_le : C ≤ g.toNat
  run_eq : X (g.toNat + 1) (D_J code 0) s0 =
    X ((g.subNat C).toNat + 1) (D_J code 0) s
  code_eq : s.executionEnv.code = code
  gas_eq : s.machineState.gasAvailable = g.subNat C
  env_eq : s.executionEnv = ee
  world_eq : s.σ₀ = s0.σ₀

theorem rd_remainingGas {code ee g s0 pc stk mem aw data σ k C}
    (h : RD code ee g s0 pc stk mem aw data σ k C) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨
      ∃ s, RunRemainder code ee g s0 C s ∧ s.machineState.pc = pc ∧
        s.machineState.stack = stk ∧ s.machineState.memory = mem ∧
        s.machineState.activeWords = aw ∧ s.machineState.returnData = data ∧ s.accountMap = σ := by
  obtain hoog | ⟨s, hX, hc, hp, ht, hg, hk, hC, hm, ha, hd, hs, he, hw⟩ := h
  · exact Or.inl hoog
  · refine Or.inr ⟨s, ⟨hC, hX.trans ?_, hc, hg, he, hw⟩, hp, ht, hm, ha, hd, hs⟩
    apply X_eq_of_gas_lt_fuel <;> simp only [hg, Sat256.subNat_toNat] <;> omega

theorem RunRemainder.start {code ee g s0 C s}
    (h : RunRemainder code ee g s0 C s) :
    RD code ee (g.subNat C) s s.machineState.pc s.machineState.stack
      s.machineState.memory s.machineState.activeWords s.machineState.returnData s.accountMap 0 0 :=
  .startWith h.code_eq rfl rfl (by simpa using h.gas_eq) (by omega) (by omega)
    (by simp) rfl rfl rfl rfl h.env_eq rfl

theorem RunRemainder.compose {code ee g s0 C s pc stk mem aw data σ k' C'}
    (h : RunRemainder code ee g s0 C s)
    (hr : RD code ee (g.subNat C) s pc stk mem aw data σ k' C') :
    RD code ee g s0 pc stk mem aw data σ (C + k') (C + C') := by
  obtain hoog | ⟨s', hX, hc, hp, ht, hg, hk, hC, hm, ha, hd, hs, he, hw⟩ := hr
  · exact Or.inl (h.run_eq.trans hoog)
  · refine Or.inr ⟨s', h.run_eq.trans hX |>.trans ?_, hc, hp, ht,
      by simpa only [Sat256.subNat_subNat] using hg, by omega, ?_, hm, ha, hd, hs, he,
      hw.trans h.world_eq⟩
    · congr 1
      simp only [Sat256.subNat_toNat]
      have := h.cost_le
      omega
    · simp only [Sat256.subNat_toNat] at hC
      have := h.cost_le
      omega

theorem RunRemainder.revert {code ee g s0 C s}
    (h : RunRemainder code ee g s0 C s) (hr : RDrev code (g.subNat C) s) :
    RDrev code g s0 := by
  obtain hoog | ⟨g', out, hr⟩ := hr
  · exact Or.inl (h.run_eq.trans hoog)
  · exact Or.inr ⟨g', out, h.run_eq.trans hr⟩

theorem RunRemainder.staticViolation {code ee g s0 C s}
    (h : RunRemainder code ee g s0 C s) (hr : RDstatic code (g.subNat C) s) :
    RDstatic code g s0 :=
  hr.elim (fun hoog ↦ Or.inl (h.run_eq.trans hoog))
    (fun hstatic ↦ Or.inr (h.run_eq.trans hstatic))

theorem RunRemainder.sourceIn {code ee g s0 C s σ evm}
    (h : RunRemainder code ee g s0 C s) (hs : SourceState s0 ee σ evm) :
    SourceState s ee σ evm :=
  ⟨hs.world.trans h.world_eq.symm, hs.env, hs.accounts⟩

theorem RunRemainder.sourceOut {code ee g s0 C s σ evm}
    (h : RunRemainder code ee g s0 C s) (hs : SourceState s ee σ evm) :
    SourceState s0 ee σ evm :=
  ⟨hs.world.trans h.world_eq, hs.env, hs.accounts⟩

end Benchmarks.CompoundIII.Comet

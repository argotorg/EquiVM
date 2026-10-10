import Benchmarks.UniswapV4PoolManager.MemoryGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES memoryPaidByGas_after_Z_target to retain the exact incoming budget.
theorem memoryCostGas_after_Z_le {validJumps : Array UInt256} {w : Operation}
    {state stateZ : State} {cost : Nat} (hZ : Z validJumps w state = .ok (stateZ, cost)) :
    Cₘ (.ofNat (memoryExpansionWords state w))+stateZ.machineState.gasAvailable.toNat ≤
      Cₘ state.machineState.activeWords+state.machineState.gasAvailable.toNat := by
  have hwords := memoryExpansionWords_lt_uint256_size state w
  have hactive := memoryExpansionWords_ge_active state w
  have hmono : Cₘ state.machineState.activeWords ≤ Cₘ (.ofNat (memoryExpansionWords state w)) := by
    rw [← u256_ofNat_toNat state.machineState.activeWords]
    exact Cₘ_monotone_of_lt hactive hwords
  have hmem := Z_memoryExpansionCost_le hZ
  have hgas := Z_gasAvailable_eq hZ
  rw [memoryExpansionCost_eq] at hmem hgas
  rw [hgas]
  omega

-- LIBRARY CANDIDATE: expansion depends only on the stack and active word count.
theorem memoryExpansionWords_congr {a b : State} (w : Operation)
    (hs : a.machineState.stack = b.machineState.stack)
    (ha : a.machineState.activeWords = b.machineState.activeWords) :
    memoryExpansionWords a w = memoryExpansionWords b w := by
  cases w <;> rename_i op <;> cases op <;> simp only [memoryExpansionWords, hs, ha]

-- LIBRARY CANDIDATE: remaining gas plus paid memory cost never increases during a step.
theorem Xstep_memoryCostGas_le {validJumps : Array UInt256} {state state' : State}
    {result : Option (HaltCause × ByteArray)}
    (h : Xstep validJumps state = .ok (state', result)) :
    Cₘ state'.machineState.activeWords+state'.machineState.gasAvailable.toNat ≤
      Cₘ state.machineState.activeWords+state.machineState.gasAvailable.toNat := by
  unfold Xstep at h
  cases hinstr : (decode state.executionEnv.code state.machineState.pc).getD (.STOP, none) with
  | mk w arg =>
    simp [hinstr, bind, Except.bind] at h
    cases hZ : Z validJumps w state <;> simp [hZ] at h
    rename_i z
    rcases z with ⟨stateZ, cost⟩
    cases hstep : step cost (w, arg) {stateZ with executionEnv.depth := state.executionEnv.depth} <;>
      simp [hstep] at h
    rename_i stateStep
    have htarget := memoryCostGas_after_Z_le (by simpa using hZ)
    have hsame := Z_stack_active_eq (by simpa using hZ)
    have he : memoryExpansionWords {stateZ with executionEnv.depth := state.executionEnv.depth} w =
        memoryExpansionWords state w := memoryExpansionWords_congr w hsame.1 hsame.2.1
    have hactive := step_activeWords_le_memoryExpansionWords hstep
    rw [he] at hactive
    have hmono : Cₘ stateStep.machineState.activeWords ≤ Cₘ (.ofNat (memoryExpansionWords state w)) := by
      rw [← u256_ofNat_toNat stateStep.machineState.activeWords]
      exact Cₘ_monotone_of_lt hactive (memoryExpansionWords_lt_uint256_size state w)
    have hgas := step_gas_le (w := w) (arg := arg)
      (s := {stateZ with executionEnv.depth := state.executionEnv.depth}) hstep
    have hle := (Nat.add_le_add hmono hgas).trans htarget
    repeat' (split at h)
    all_goals
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      exact hle

theorem X_success_memoryCostGas_le {fuel : Nat} {validJumps : Array UInt256}
    {state state' : State} {out : ByteArray}
    (h : X fuel validJumps state = .ok (.success state' out)) :
    Cₘ state'.machineState.activeWords+state'.machineState.gasAvailable.toNat ≤
      Cₘ state.machineState.activeWords+state.machineState.gasAvailable.toNat := by
  induction fuel generalizing state with
  | zero => simp [X] at h
  | succ fuel ih =>
    unfold X at h
    simp only [bind, Except.bind] at h
    cases hstep : Xstep validJumps state with
    | error e => simp [hstep] at h
    | ok res =>
      rcases res with ⟨state₁, ret⟩
      simp only [hstep] at h
      have hle := Xstep_memoryCostGas_le hstep
      cases ret with
      | none => exact (ih h).trans hle
      | some halted =>
        rcases halted with ⟨cause, haltOut⟩
        cases cause <;> simp at h
        rcases h with ⟨rfl, rfl⟩
        exact hle

end Benchmarks.UniswapV4PoolManager

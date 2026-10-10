import Benchmarks.UniswapV4PoolManager.RecursiveOperationPotential
import Benchmarks.UniswapV4PoolManager.CalleeMemoryGas

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: remaining gas, charged memory, and the minimum work represented by current data.
noncomputable def executionPotential (s : State) : Nat :=
  Cₘ s.machineState.activeWords+operationPotential s+s.machineState.gasAvailable.toNat

theorem step_operationPotentialGas_return {gasCost : Nat} {w : Operation}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (hle : gasCost ≤ s.machineState.gasAvailable.toNat)
    (hcost : gasCost = C' s w) (h : step gasCost (w, arg) s = .ok s') :
    operationPotential s'+s'.machineState.gasAvailable.toNat+(if w = .RETURN then 4 else 0) ≤
      operationPotential s+s.machineState.gasAvailable.toNat := by
  by_cases hw : w = .RETURN
  · subst w
    rw [if_pos rfl]
    have hp := (step_return_potential h).1
    have hg := step_gas_le h
    omega
  · rw [if_neg hw, Nat.add_zero]
    exact step_operationPotentialGas_le hle hcost h

theorem Xstep_executionPotential_return {validJumps : Array UInt256} {s s' : State}
    {result : Option (HaltCause × ByteArray)}
    (h : Xstep validJumps s = .ok (s', result)) :
    executionPotential s'+
        (if ((decode s.executionEnv.code s.machineState.pc).getD (.STOP, none)).1 = .RETURN then 4 else 0) ≤
      executionPotential s := by
  unfold Xstep at h
  cases hinstr : (decode s.executionEnv.code s.machineState.pc).getD (.STOP, none) with
  | mk w arg =>
    simp [hinstr, bind, Except.bind] at h
    cases hZ : Z validJumps w s <;> simp [hZ] at h
    rename_i z
    rcases z with ⟨stateZ, cost⟩
    cases hstep : step cost (w, arg) {stateZ with executionEnv.depth := s.executionEnv.depth} <;>
      simp [hstep] at h
    rename_i stateStep
    have hm := memoryCostGas_after_Z_le (by simpa using hZ)
    have heq := Z_stack_active_eq (by simpa using hZ)
    have hop : operationPotential {stateZ with executionEnv.depth := s.executionEnv.depth} =
        operationPotential s := by simp only [operationPotential, heq.1, heq.2.2]
    have he : memoryExpansionWords {stateZ with executionEnv.depth := s.executionEnv.depth} w =
        memoryExpansionWords s w := memoryExpansionWords_congr w heq.1 heq.2.1
    have ha := step_activeWords_le_memoryExpansionWords hstep
    rw [he] at ha
    have hcm : Cₘ stateStep.machineState.activeWords ≤ Cₘ (.ofNat (memoryExpansionWords s w)) := by
      rw [← u256_ofNat_toNat stateStep.machineState.activeWords]
      exact Cₘ_monotone_of_lt ha (memoryExpansionWords_lt_uint256_size s w)
    have hc : cost = C' {stateZ with executionEnv.depth := s.executionEnv.depth} w := by
      rw [C'_set_depth]
      exact Z_cost_eq_C' (by simpa using hZ)
    have hpaid := Z_cost_le (evmState' := stateZ) (by simpa using hZ)
    have hp := step_operationPotentialGas_return
      (s := {stateZ with executionEnv.depth := s.executionEnv.depth}) hpaid hc hstep
    rw [hop] at hp
    have htotal : executionPotential stateStep+(if w = .RETURN then 4 else 0) ≤ executionPotential s := by
      dsimp only [executionPotential] at hp ⊢
      omega
    repeat' (split at h)
    all_goals
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      simpa only [executionPotential, operationPotential, hinstr] using htotal

theorem Xstep_executionPotential_le {validJumps : Array UInt256} {s s' : State}
    {result : Option (HaltCause × ByteArray)}
    (h : Xstep validJumps s = .ok (s', result)) : executionPotential s' ≤ executionPotential s := by
  have := Xstep_executionPotential_return h
  omega

end Benchmarks.UniswapV4PoolManager

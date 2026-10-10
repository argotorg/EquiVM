import Benchmarks.UniswapV4PoolManager.StepCallOperationGas
import Benchmarks.UniswapV4PoolManager.OperationPotentialCost

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

theorem step_recursive_potential {gasCost : Nat} {w : Operation}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (hr : RecursiveSystemStep w) (h : step gasCost (w, arg) s = .ok s') :
    operationPotential s' ≤ operationPotential s+16 := by
  cases w <;> try simp [RecursiveSystemStep] at hr
  rename_i op
  cases op <;> try simp at hr
  all_goals try contradiction
  all_goals
    rw [step.eq_1] at h
    simp [bind, Except.bind, pure, Except.pure,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
    repeat (first | simp at h | split at h)
    rename_i _ popped hp _ result hcall
    rcases result with ⟨x, state⟩
    have hpop := option_liftM_eq_some hp
    first
    | have hs := pop3_length hpop
    | have hs := pop4_length hpop
    | have hs := pop6_length hpop
    | have hs := pop7_length hpop
    have hf := memoryFootprint_le s'.machineState.memory
    rw [← h] at hf ⊢
    simp only [operationPotential, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      Stack.push, List.length_cons] at hs hf ⊢
    omega

theorem step_recursive_gas_100 {gasCost : Nat} {w : Operation}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (hr : RecursiveSystemStep w) (hle : gasCost ≤ s.machineState.gasAvailable.toNat)
    (hcost : gasCost = C' s w) (h : step gasCost (w, arg) s = .ok s') :
    s'.machineState.gasAvailable.toNat+100 ≤ s.machineState.gasAvailable.toNat := by
  cases w <;> try simp [RecursiveSystemStep] at hr
  rename_i op
  cases op <;> try simp at hr
  all_goals try contradiction
  · have hg := step_create_gas_cost hle h
    have hc : 100 ≤ gasCost := by
      rw [hcost]
      change 100 ≤ 32000+_
      omega
    omega
  · exact step_call_gas_100 hle hcost h
  · exact step_callcode_gas_100 hle hcost h
  · exact step_delegatecall_gas_100 hle hcost h
  · have hg := step_create2_gas_cost hle h
    have hc : 100 ≤ gasCost := by
      rw [hcost]
      change 100 ≤ 32000+_+_
      omega
    omega
  · exact step_staticcall_gas_100 hle hcost h

-- LIBRARY CANDIDATE: operation gas pays for stack supply and nonzero memory footprint.
theorem step_operationPotentialGas_le {gasCost : Nat} {w : Operation}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (hle : gasCost ≤ s.machineState.gasAvailable.toNat)
    (hcost : gasCost = C' s w) (h : step gasCost (w, arg) s = .ok s') :
    operationPotential s'+s'.machineState.gasAvailable.toNat ≤
      operationPotential s+s.machineState.gasAvailable.toNat := by
  by_cases hr : RecursiveSystemStep w
  · have hp := step_recursive_potential hr h
    have hg := step_recursive_gas_100 hr hle hcost h
    omega
  · have hp := step_nonrecursive_operationPotential hr h
    rw [← hcost] at hp
    have hg := step_nonrecursive_gas hr h
    rw [hg, Sat256.subNat_toNat]
    omega

end Benchmarks.UniswapV4PoolManager

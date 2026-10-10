import Benchmarks.UniswapV4PoolManager.OperationPotentialMemory
import Benchmarks.UniswapV4PoolManager.OperationPotentialControl

open Ethereum Ethereum.EVM Reasoning.Theory
open GasConstants InstructionGasGroups
namespace Benchmarks.UniswapV4PoolManager

theorem Caccess_ge_100 (addr : AccountAddress) (A : Substate) : 100 ≤ Caccess addr A := by
  unfold Caccess
  split <;> decide

theorem C'_env_ge_two (s : State) (op : Operation.EOp) : 2 ≤ C' s (.Env op) := by
  cases op <;>
    simp [C', Wzero, Wbase, Wverylow, Wlow, Wmid, Whigh, Wcopy, Wextaccount,
      Gbase, Gverylow, Gcopy, Caccess, Gwarmaccess, Gcoldaccountaccess] <;>
    first | omega | split <;> omega

theorem C'_block_ge_two (s : State) (op : Operation.BOp) : 2 ≤ C' s (.Block op) := by
  cases op <;> exact of_decide_eq_true rfl

theorem C'_push_ge_two (s : State) (op : Operation.POp) : 2 ≤ C' s (.Push op) := by
  cases op <;> exact of_decide_eq_true rfl

theorem C'_dup_ge_two (s : State) (op : Operation.DOp) : 2 ≤ C' s (.Dup op) := by
  cases op <;> exact of_decide_eq_true rfl

theorem step_env_cost_potential {gasCost : Nat} {op : Operation.EOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.Env op, arg) s = .ok s') :
    operationPotential s' ≤ operationPotential s+C' s (.Env op) := by
  by_cases hn : (.Env op : Operation) ∈ [.CALLDATACOPY, .CODECOPY, .EXTCODECOPY, .RETURNDATACOPY]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with hcopy | hcopy | hcopy | hcopy
    · have hb := step_calldatacopy_potential (by simpa only [hcopy] using h)
      simpa only [hcopy, C', Wcopy, List.mem_cons, List.mem_singleton, or_true,
        true_or, if_true, Gverylow, Gcopy, Nat.add_assoc] using hb
    · have hb := step_codecopy_potential (by simpa only [hcopy] using h)
      simpa only [hcopy, C', Wcopy, List.mem_cons, List.mem_singleton, or_true,
        true_or, if_true, Gverylow, Gcopy, Nat.add_assoc] using hb
    · have hb := step_extcodecopy_potential (by simpa only [hcopy] using h)
      rw [hcopy]
      change operationPotential s' ≤ operationPotential s+(Caccess _ _+3*((s.machineState.stack[3]!.toNat+31)/32))
      exact hb.trans (Nat.add_le_add_left ((show 6 ≤ 100 by decide).trans
        ((Caccess_ge_100 _ _).trans (Nat.le_add_right _ _))) _)
    · have hb := step_returndatacopy_potential (by simpa only [hcopy] using h)
      simpa only [hcopy, C', Wcopy, List.mem_cons, List.mem_singleton, or_true,
        true_or, if_true, Gverylow, Gcopy, Nat.add_assoc] using hb
  · have hp := step_env_noncopy_potential hn h
    have hc := C'_env_ge_two s op
    omega

theorem step_stackmemflow_cost_potential {gasCost : Nat} {op : Operation.SMSFOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.StackMemFlow op, arg) s = .ok s') :
    operationPotential s' ≤ operationPotential s+C' s (.StackMemFlow op) := by
  by_cases hn : (.StackMemFlow op : Operation) ∈ [.MSTORE, .MSTORE8, .MCOPY, .PC, .MSIZE, .GAS]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with ho | ho | ho | ho | ho | ho
    · have hb := step_mstore_potential (by simpa only [ho] using h)
      rw [ho]
      exact hb
    · have hb := step_mstore8_potential (by simpa only [ho] using h)
      rw [ho]
      exact hb
    · have hb := step_mcopy_potential (by simpa only [ho] using h)
      rw [ho]
      simpa only [C', Wcopy, List.mem_cons, List.mem_singleton, or_true,
        true_or, if_true, Gverylow, Gcopy, Nat.add_assoc] using hb
    · have hb := step_pc_potential (by simpa only [ho] using h)
      rw [ho]
      exact Nat.le_of_eq hb
    · have hb := step_msize_potential (by simpa only [ho] using h)
      rw [ho]
      exact Nat.le_of_eq hb
    · have hb := step_gas_potential (by simpa only [ho] using h)
      rw [ho]
      exact Nat.le_of_eq hb
  · exact (step_stackmemflow_other_potential hn h).trans (Nat.le_add_right _ _)

theorem step_selfdestruct_potential {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.SELFDESTRUCT, arg) s = .ok s') :
    operationPotential s' ≤ operationPotential s+12 := by
  have hf := memoryFootprint_le s'.machineState.memory
  rw [step.eq_1] at h
  dsimp only at h
  split at h
  · rename_i rest addr hp
    have hs := pop_length hp
    split at h <;> simp only [Except.ok.injEq] at h <;> subst s' <;>
      dsimp only [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, operationPotential] at hs hf ⊢ <;>
      omega
  · contradiction

-- LIBRARY CANDIDATE: nonrecursive opcodes pay for their change in stack and memory footprint.
theorem step_nonrecursive_operationPotential {gasCost : Nat} {w : Operation}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (hn : ¬RecursiveSystemStep w) (h : step gasCost (w, arg) s = .ok s') :
    operationPotential s' ≤ operationPotential s+C' s w := by
  cases w with
  | StopArith op => exact (step_stoparith_potential h).trans (Nat.le_add_right _ _)
  | CompBit op => exact (step_compbit_potential h).trans (Nat.le_add_right _ _)
  | Keccak op => exact (step_keccak_potential h).trans (Nat.le_add_right _ _)
  | Env op => exact step_env_cost_potential h
  | StackMemFlow op => exact step_stackmemflow_cost_potential h
  | Block op => have hp := step_block_potential h; have hc := C'_block_ge_two s op; omega
  | Push op => have hp := step_push_potential h; have hc := C'_push_ge_two s op; omega
  | Dup op => have hp := step_dup_potential h; have hc := C'_dup_ge_two s op; omega
  | Exchange op => exact (Nat.le_of_eq (step_exchange_potential h)).trans (Nat.le_add_right _ _)
  | Log op => exact (step_log_potential h).trans (Nat.le_add_right _ _)
  | System op =>
    cases op <;> simp only [RecursiveSystemStep, List.mem_cons, List.mem_singleton, not_or] at hn
    all_goals try contradiction
    · have hp := (step_return_potential h).1
      omega
    · exact (step_revert_potential h).trans (Nat.le_add_right _ _)
    · rw [step.eq_1] at h; contradiction
    · have hp := step_selfdestruct_potential h
      have hc : 12 ≤ C' s .SELFDESTRUCT := by
        change 12 ≤ Gselfdestruct+_+_
        change 12 ≤ 5000+_+_
        omega
      exact hp.trans (Nat.add_le_add_left hc _)

end Benchmarks.UniswapV4PoolManager

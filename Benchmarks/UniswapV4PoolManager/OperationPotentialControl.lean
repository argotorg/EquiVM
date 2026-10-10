import Benchmarks.UniswapV4PoolManager.OperationPotentialPure

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

theorem sstore_memory (s : State) (slot value : UInt256) :
    (s.sstore slot value).machineState.memory = s.machineState.memory := by
  unfold Ethereum.State.sstore
  cases hlookup : s.lookupAccount s.executionEnv.codeOwner <;>
    simp [Option.option, hlookup, Ethereum.State.setAccount, Ethereum.State.addAccessedStorageKey]

theorem tstore_memory (s : State) (slot value : UInt256) :
    (s.tstore slot value).machineState.memory = s.machineState.memory := by
  unfold Ethereum.State.tstore
  cases hlookup : s.lookupAccount s.executionEnv.codeOwner <;>
    simp [Option.option, hlookup, Ethereum.State.updateAccount]

theorem step_stackmemflow_other_potential {gasCost : Nat} {op : Operation.SMSFOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (hn : (.StackMemFlow op : Operation) ∉ [.MSTORE, .MSTORE8, .MCOPY, .PC, .MSIZE, .GAS])
    (h : step gasCost (.StackMemFlow op, arg) s = .ok s') :
    operationPotential s' ≤ operationPotential s := by
  cases op <;> simp only [List.mem_cons, List.mem_singleton, not_or] at hn
  all_goals try contradiction
  all_goals rw [step.eq_1] at h
  all_goals first
  | exact Nat.le_of_eq (by simpa only [operationPotential] using unaryStateOp_potential (fun _ => rfl) h)
  | simpa only [operationPotential] using binaryStateOp_potential (sstore_memory _) h
  | simpa only [operationPotential] using binaryStateOp_potential (tstore_memory _) h
  | simp only [Except.ok.injEq] at h
    subst s'
    exact Nat.le_refl _
  | skip
  all_goals
    dsimp only at h
    split at h
    · rename_i hp
      first
      | have hs := pop_length hp
      | have hs := pop2_length hp
      simp only [Id.run, Except.ok.injEq] at h
      subst s'
      simp only [operationPotential, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
        MachineState.mload, Stack.push, List.length_cons] at hs ⊢
      omega
    · contradiction

theorem step_pc_potential {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.PC, arg) s = .ok s') : operationPotential s' = operationPotential s+2 := by
  rw [step.eq_1] at h
  simp only [Except.ok.injEq] at h
  subst s'
  simp only [operationPotential, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
    Stack.push, List.length_cons]
  omega

theorem step_msize_potential {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.MSIZE, arg) s = .ok s') : operationPotential s' = operationPotential s+2 := by
  rw [step.eq_1] at h
  simpa only [operationPotential] using machineStateOp_potential h

theorem step_gas_potential {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.GAS, arg) s = .ok s') : operationPotential s' = operationPotential s+2 := by
  rw [step.eq_1] at h
  simpa only [operationPotential] using machineStateOp_potential h

theorem step_log_potential {gasCost : Nat} {op : Operation.LOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.Log op, arg) s = .ok s') :
    operationPotential s' ≤ operationPotential s := by
  cases op <;> rw [step.eq_1] at h <;>
    simp only [log0Op, log1Op, log2Op, log3Op, log4Op, Id.run] at h
  all_goals split at h
  all_goals try contradiction
  all_goals
    rename_i hp
    first
    | have hs := pop2_length hp
    | have hs := pop3_length hp
    | have hs := pop4_length hp
    | have hs := pop5_length hp
    | have hs := pop6_length hp
    simp only [Except.ok.injEq] at h
    subst s'
    simp only [operationPotential, evmLogOp, logOp,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at hs ⊢
    omega

theorem step_return_potential {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.RETURN, arg) s = .ok s') :
    operationPotential s'+4 = operationPotential s ∧ s'.machineState.memory = s.machineState.memory := by
  rw [step.eq_1] at h
  simp only [binaryMachineStateOp, Id.run] at h
  split at h
  · rename_i rest off len hp
    have hs := pop2_length hp
    simp only [Except.ok.injEq] at h
    subst s'
    simp only [operationPotential, MachineState.evmReturn, MachineState.setReturnData,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at hs ⊢
    exact ⟨by omega, True.intro⟩
  · contradiction

theorem step_revert_potential {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.REVERT, arg) s = .ok s') :
    operationPotential s' ≤ operationPotential s := by
  rw [step.eq_1] at h
  simp only [binaryMachineStateOp, Id.run] at h
  split at h
  · rename_i rest off len hp
    have hs := pop2_length hp
    simp only [Except.ok.injEq] at h
    subst s'
    simp only [operationPotential, MachineState.evmRevert, MachineState.evmReturn, MachineState.setReturnData,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at hs ⊢
    omega
  · contradiction

end Benchmarks.UniswapV4PoolManager

import Benchmarks.UniswapV4PoolManager.OperationPotential

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

theorem executionEnvOp_potential {f : ExecutionEnv → UInt256} {s s' : State}
    (h : executionEnvOp f s = .ok s') : operationPotential s' = operationPotential s+2 := by
  simp only [executionEnvOp, Id.run, Except.ok.injEq] at h
  subst s'
  simp only [operationPotential, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
    Stack.push, List.length_cons]
  omega

theorem machineStateOp_potential {f : MachineState → UInt256} {s s' : State}
    (h : machineStateOp f s = .ok s') : operationPotential s' = operationPotential s+2 := by
  simp only [machineStateOp, Id.run, Except.ok.injEq] at h
  subst s'
  simp only [operationPotential, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
    Stack.push, List.length_cons]
  omega

theorem stateOp_potential {f : State → UInt256} {s s' : State}
    (h : stateOp f s = .ok s') : operationPotential s' = operationPotential s+2 := by
  simp only [stateOp, Id.run, Except.ok.injEq] at h
  subst s'
  simp only [operationPotential, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
    Stack.push, List.length_cons]
  omega

theorem unaryExecutionEnvOp_potential {f : ExecutionEnv → UInt256 → UInt256} {s s' : State}
    (h : unaryExecutionEnvOp f s = .ok s') : operationPotential s' = operationPotential s := by
  unfold unaryExecutionEnvOp at h
  split at h
  · rename_i rest a hp
    have hs := pop_length hp
    simp only [Id.run, Except.ok.injEq] at h
    subst s'
    simp only [operationPotential, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      Stack.push, List.length_cons, hs]
  · contradiction

theorem unaryStateOp_potential {f : State → UInt256 → State × UInt256} {s s' : State}
    (hf : ∀ a, (f s a).1.machineState.memory = s.machineState.memory)
    (h : unaryStateOp f s = .ok s') : operationPotential s' = operationPotential s := by
  unfold unaryStateOp at h
  split at h
  · rename_i rest a hp
    have hs := pop_length hp
    simp only [Id.run, Except.ok.injEq] at h
    subst s'
    simp only [operationPotential, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      Stack.push, List.length_cons, hs, hf]
  · contradiction

theorem binaryStateOp_potential {f : State → UInt256 → UInt256 → State} {s s' : State}
    (hf : ∀ a b, (f s a b).machineState.memory = s.machineState.memory)
    (h : binaryStateOp f s = .ok s') : operationPotential s' ≤ operationPotential s := by
  unfold binaryStateOp at h
  split at h
  · rename_i rest a b hp
    have hs := pop2_length hp
    simp only [Id.run, Except.ok.injEq] at h
    subst s'
    simp only [operationPotential, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      hs, hf]
    omega
  · contradiction

theorem step_keccak_potential {gasCost : Nat} {op : Operation.KOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.Keccak op, arg) s = .ok s') :
    operationPotential s' ≤ operationPotential s := by
  cases op
  rw [step.eq_1] at h
  simp only [binaryMachineStateOp', Id.run] at h
  split at h
  · rename_i rest a b hp
    have hs := pop2_length hp
    simp only [MachineState.keccak256, Except.ok.injEq] at h
    subst s'
    simp only [operationPotential, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      Stack.push, List.length_cons, hs]
    omega
  · contradiction

theorem step_block_potential {gasCost : Nat} {op : Operation.BOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.Block op, arg) s = .ok s') :
    operationPotential s' ≤ operationPotential s+2 := by
  cases op <;> rw [step.eq_1] at h
  all_goals first
  | exact Nat.le_of_eq (by simpa only [operationPotential] using executionEnvOp_potential h)
  | exact Nat.le_of_eq (by simpa only [operationPotential] using stateOp_potential h)
  | have he := unaryExecutionEnvOp_potential h
    dsimp only [operationPotential] at he ⊢
    omega
  | have he := unaryStateOp_potential (fun _ => rfl) h
    dsimp only [operationPotential] at he ⊢
    omega

theorem step_env_noncopy_potential {gasCost : Nat} {op : Operation.EOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (hn : (.Env op : Operation) ∉ [.CALLDATACOPY, .CODECOPY, .EXTCODECOPY, .RETURNDATACOPY])
    (h : step gasCost (.Env op, arg) s = .ok s') :
    operationPotential s' ≤ operationPotential s+2 := by
  cases op <;> simp only [List.mem_cons, List.mem_singleton, not_or] at hn
  all_goals try contradiction
  all_goals rw [step.eq_1] at h
  all_goals first
  | exact Nat.le_of_eq (by simpa only [operationPotential] using executionEnvOp_potential h)
  | exact Nat.le_of_eq (by simpa only [operationPotential] using machineStateOp_potential h)
  | have he := unaryStateOp_potential (fun _ => rfl) h
    dsimp only [operationPotential] at he ⊢
    omega
  | have he := unaryStateOp_potential (by
        intro a
        dsimp only [Ethereum.State.extCodeHash]
        split <;> rfl) h
    dsimp only [operationPotential] at he ⊢
    omega

theorem step_push_potential {gasCost : Nat} {op : Operation.POp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.Push op, arg) s = .ok s') :
    operationPotential s' = operationPotential s+2 := by
  cases op <;> rw [step.eq_1] at h <;>
    simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals repeat' (split at h)
  all_goals first
  | contradiction
  | simp only [Except.ok.injEq] at h
    subst s'
    simp only [operationPotential, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      Stack.push, List.length_cons]
    omega

theorem dup_potential {n : Nat} {s s' : State} (h : dup n s = .ok s') :
    operationPotential s' = operationPotential s+2 := by
  simp only [dup] at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst s'
    simp only [operationPotential, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      List.length_cons]
    omega
  · contradiction

theorem step_dup_potential {gasCost : Nat} {op : Operation.DOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.Dup op, arg) s = .ok s') :
    operationPotential s' = operationPotential s+2 := by
  cases op <;> rw [step.eq_1] at h <;>
    simpa only [operationPotential] using dup_potential h

theorem swap_potential {n : Nat} {s s' : State} (hn : 0 < n) (h : swap n s = .ok s') :
    operationPotential s' = operationPotential s := by
  simp only [swap] at h
  split at h
  · rename_i hs
    have htail : ((s.machineState.stack.take (n+1)).tail!).length = n := by
      cases he : s.machineState.stack.take (n+1) with
      | nil => simp only [he, List.length_nil] at hs; omega
      | cons x xs => simpa only [he, List.length_cons, List.tail!_cons, Nat.add_right_cancel_iff] using hs
    simp only [Except.ok.injEq] at h
    subst s'
    simp only [operationPotential, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      List.length_cons, List.length_append, List.length_dropLast, htail, List.length_nil,
      List.length_take, List.length_drop] at hs ⊢
    omega
  · contradiction

theorem step_exchange_potential {gasCost : Nat} {op : Operation.ExOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.Exchange op, arg) s = .ok s') :
    operationPotential s' = operationPotential s := by
  cases op <;> rw [step.eq_1] at h <;>
    simpa only [operationPotential] using swap_potential (by decide) h

end Benchmarks.UniswapV4PoolManager

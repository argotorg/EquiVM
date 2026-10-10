import Benchmarks.UniswapV4PoolManager.OperationPotential

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

theorem pop3_stack {stack rest : Stack UInt256} {a b c : UInt256}
    (h : stack.pop3 = some (rest, a, b, c)) : stack = a::b::c::rest := by
  rcases stack with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp_all [Stack.pop3]

theorem pop4_stack {stack rest : Stack UInt256} {a b c d : UInt256}
    (h : stack.pop4 = some (rest, a, b, c, d)) : stack = a::b::c::d::rest := by
  rcases stack with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;> simp_all [Stack.pop4]

theorem memoryFootprint_write_copy (src mem : ByteArray) (srcOff dest len : Nat) :
    memoryFootprint (src.write srcOff mem dest len) ≤ memoryFootprint mem+9+3*((len+31)/32) := by
  by_cases hl : len ≤ 32
  · have := memoryFootprint_write_short src mem srcOff dest len hl
    omega
  · have := memoryFootprint_le (src.write srcOff mem dest len)
    omega

theorem step_mstore_potential {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.MSTORE, arg) s = .ok s') :
    operationPotential s' ≤ operationPotential s+3 := by
  rw [step.eq_1] at h
  simp only [binaryMachineStateOp, Id.run] at h
  split at h
  · rename_i rest dest word hp
    have hs := pop2_length hp
    have hf := memoryFootprint_write_short word.toByteArray s.machineState.memory 0 dest.toNat 32 (by omega)
    simp only [Except.ok.injEq] at h
    subst s'
    dsimp only [MachineState.mstore, MachineState.writeWord, writeBytes,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, operationPotential] at hs ⊢
    omega
  · contradiction

theorem step_mstore8_potential {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.MSTORE8, arg) s = .ok s') :
    operationPotential s' ≤ operationPotential s+3 := by
  rw [step.eq_1] at h
  simp only [binaryMachineStateOp, Id.run] at h
  split at h
  · rename_i rest dest word hp
    have hs := pop2_length hp
    have hf := memoryFootprint_write_short ⟨#[UInt8.ofNat word.toNat]⟩
      s.machineState.memory 0 dest.toNat 1 (by omega)
    simp only [Except.ok.injEq] at h
    subst s'
    dsimp only [MachineState.mstore8, writeBytes,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, operationPotential] at hs ⊢
    omega
  · contradiction

theorem ternaryCopyOp_potential {f : State → UInt256 → UInt256 → UInt256 → State} {s s' : State}
    (hf : ∀ dest src len,
      memoryFootprint (f s dest src len).machineState.memory ≤
        memoryFootprint s.machineState.memory+9+3*((len.toNat+31)/32))
    (h : ternaryCopyOp f s = .ok s') :
    operationPotential s' ≤ operationPotential s+3+3*((s.machineState.stack[2]!.toNat+31)/32) := by
  unfold ternaryCopyOp at h
  split at h
  · rename_i rest dest src len hp
    have hs := pop3_stack hp
    have hb := hf dest src len
    simp only [Id.run, Except.ok.injEq] at h
    subst s'
    simp only [operationPotential, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      hs, List.length_cons, List.getElem!_cons_succ, List.getElem!_cons_zero]
    omega
  · contradiction

theorem step_calldatacopy_potential {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.CALLDATACOPY, arg) s = .ok s') :
    operationPotential s' ≤ operationPotential s+3+3*((s.machineState.stack[2]!.toNat+31)/32) := by
  rw [step.eq_1] at h
  simpa only [operationPotential] using ternaryCopyOp_potential (by
    intro dest src len
    exact memoryFootprint_write_copy _ _ _ _ _) h

theorem step_codecopy_potential {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.CODECOPY, arg) s = .ok s') :
    operationPotential s' ≤ operationPotential s+3+3*((s.machineState.stack[2]!.toNat+31)/32) := by
  rw [step.eq_1] at h
  simpa only [operationPotential] using ternaryCopyOp_potential (by
    intro dest src len
    exact memoryFootprint_write_copy _ _ _ _ _) h

theorem step_returndatacopy_potential {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.RETURNDATACOPY, arg) s = .ok s') :
    operationPotential s' ≤ operationPotential s+3+3*((s.machineState.stack[2]!.toNat+31)/32) := by
  rw [step.eq_1] at h
  dsimp only at h
  split at h
  · rename_i rest dest src len hp
    have hs := pop3_stack hp
    have hf := memoryFootprint_write_copy s.machineState.returnData s.machineState.memory src.toNat dest.toNat len.toNat
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst s'
    simp only [operationPotential, MachineState.returndatacopy, writeBytes,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      hs, List.length_cons, List.getElem!_cons_succ, List.getElem!_cons_zero]
    omega
  · contradiction

theorem step_mcopy_potential {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.MCOPY, arg) s = .ok s') :
    operationPotential s' ≤ operationPotential s+3+3*((s.machineState.stack[2]!.toNat+31)/32) := by
  rw [step.eq_1] at h
  simp only [ternaryMachineStateOp, Id.run] at h
  split at h
  · rename_i rest dest src len hp
    have hs := pop3_stack hp
    have hf := memoryFootprint_write_copy s.machineState.memory s.machineState.memory src.toNat dest.toNat len.toNat
    simp only [Except.ok.injEq] at h
    subst s'
    simp only [operationPotential, MachineState.mcopy, writeBytes,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      hs, List.length_cons, List.getElem!_cons_succ, List.getElem!_cons_zero]
    omega
  · contradiction

theorem step_extcodecopy_potential {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.EXTCODECOPY, arg) s = .ok s') :
    operationPotential s' ≤ operationPotential s+6 := by
  rw [step.eq_1] at h
  simp only [quaternaryCopyOp, Id.run] at h
  split at h
  · rename_i rest addr dest src len hp
    have hs := pop4_length hp
    have hf := memoryFootprint_le s'.machineState.memory
    simp only [Except.ok.injEq] at h
    subst s'
    dsimp only [operationPotential, extCodeCopy',
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at hs hf ⊢
    omega
  · contradiction

end Benchmarks.UniswapV4PoolManager

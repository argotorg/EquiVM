import Benchmarks.Midnight.Common
import Ethereum.Theory.ReturnDataBound

/-! Quantitative memory accounting, retaining the actual initial gas budget. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: quantitative versions of Ethereum.EVM.memoryPaidByGas.
def memoryCost (words : Nat) : Nat := 3 * words + words * words / 512

theorem memoryCost_mono {a b : Nat} (h : a ≤ b) : memoryCost a ≤ memoryCost b := by
  exact Nat.add_le_add (Nat.mul_le_mul_left 3 h)
    (Nat.div_le_div_right (Nat.mul_le_mul h h))

theorem memoryCost_eq_Cₘ {words : Nat} (h : words < UInt256.size) :
    memoryCost words = Cₘ (UInt256.ofNat words) := by
  simp [memoryCost, Cₘ, GasConstants.Gmemory, Cₘ.QuadraticCeofficient,
    UInt256.toNat_ofNat_of_lt h]

def memoryGas (state : State) : Nat :=
  Cₘ state.machineState.activeWords + state.machineState.gasAvailable.toNat

theorem memoryGas_after_Z {validJumps : Array UInt256} {op : Operation}
    {state stateZ : State} {cost : Nat}
    (hZ : Z validJumps op state = .ok (stateZ, cost)) :
    Cₘ (UInt256.ofNat (memoryExpansionWords state op)) +
      stateZ.machineState.gasAvailable.toNat ≤ memoryGas state := by
  have hwords := memoryExpansionWords_lt_uint256_size state op
  have hactive := memoryExpansionWords_ge_active state op
  have hmono : Cₘ state.machineState.activeWords ≤
      Cₘ (UInt256.ofNat (memoryExpansionWords state op)) := by
    conv_lhs => rw [← u256_ofNat_toNat state.machineState.activeWords]
    exact Cₘ_monotone_of_lt hactive hwords
  have hmem := Z_memoryExpansionCost_le hZ
  have hgas := Z_gasAvailable_eq hZ
  rw [memoryExpansionCost_eq] at hmem hgas
  rw [hgas]
  unfold memoryGas
  omega

theorem step_memoryGas_le_target {op : Operation} {arg : Option (UInt256 × Nat)}
    {state state' : State} {cost : Nat}
    (hstep : step cost (op, arg) state = .ok state') :
    memoryGas state' ≤ Cₘ (UInt256.ofNat (memoryExpansionWords state op)) +
      state.machineState.gasAvailable.toNat := by
  have hactive := step_activeWords_le_memoryExpansionWords hstep
  have hmono : Cₘ state'.machineState.activeWords ≤
      Cₘ (UInt256.ofNat (memoryExpansionWords state op)) := by
    conv_lhs => rw [← u256_ofNat_toNat state'.machineState.activeWords]
    exact Cₘ_monotone_of_lt hactive (memoryExpansionWords_lt_uint256_size state op)
  exact Nat.add_le_add hmono (step_gas_le hstep)

theorem Xstep_memoryGas_le {validJumps : Array UInt256} {state state' : State}
    {halt : Option (HaltCause × ByteArray)}
    (h : Xstep validJumps state = .ok (state', halt)) : memoryGas state' ≤ memoryGas state := by
  unfold Xstep at h
  cases hinstr : (decode state.executionEnv.code state.machineState.pc).getD (.STOP, none) with
  | mk op arg =>
    simp [hinstr, bind, Except.bind] at h
    cases hZ : Z validJumps op state <;> simp [hZ] at h
    rename_i z
    rcases z with ⟨stateZ, cost⟩
    cases hstep : step cost (op, arg) { stateZ with executionEnv.depth := state.executionEnv.depth }
      <;> simp [hstep] at h
    rename_i stateStep
    have hsame := Z_stack_active_eq hZ
    have htarget := memoryGas_after_Z hZ
    have hs := step_memoryGas_le_target hstep
    have he : memoryExpansionWords { stateZ with executionEnv.depth := state.executionEnv.depth } op =
        memoryExpansionWords state op := by
      simp only [memoryExpansionWords, hsame.1, hsame.2.1]
    rw [he] at hs
    have hbound := hs.trans htarget
    repeat (first | split at h | cases h)
    all_goals
      try (by_cases hrevert : op = Operation.REVERT <;> simp [hrevert] at h)
    all_goals
      try rcases h with ⟨rfl, _⟩
      subst_vars
      exact hbound

private theorem stack_eq_of_pop2 {stack tail : Stack UInt256} {a b : UInt256}
    (h : stack.pop2 = some (tail, a, b)) : stack = a :: b :: tail := by
  cases stack with
  | nil => simp [Stack.pop2] at h
  | cons x xs =>
    cases xs with
    | nil => simp [Stack.pop2] at h
    | cons y ys => simp_all [Stack.pop2]

theorem step_return_output_words {cost : Nat} {arg : Option (UInt256 × Nat)}
    {state state' : State} {op : Operation} (hop : op = .RETURN ∨ op = .REVERT)
    (h : step cost (op, arg) state = .ok state') :
    state'.machineState.H_return.size ≤ 32 * memoryExpansionWords state op := by
  rcases hop with rfl | rfl <;>
    (unfold step at h
     simp [binaryMachineStateOp] at h
     cases hpop : state.machineState.stack.pop2 with
     | none => simp [hpop] at h
     | some popped =>
       rcases popped with ⟨stack, offset, len⟩
       have hstack := stack_eq_of_pop2 hpop
       simp [hpop, MachineState.evmReturn, MachineState.evmRevert,
         Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
       injection h with hstate
       subst state'
       simpa [memoryExpansionWords, hstack, MachineState.evmReturn] using
         MachineState.evmReturn_H_return_size_le_words_mul
           { state.machineState with
             execLength := state.machineState.execLength + 1
             gasAvailable := state.machineState.gasAvailable.subNat cost } offset len)

theorem return_output_memoryCost {validJumps : Array UInt256} {op : Operation}
    {state stateZ state' : State} {cost : Nat} {arg : Option (UInt256 × Nat)}
    (hop : op = .RETURN ∨ op = .REVERT)
    (hZ : Z validJumps op state = .ok (stateZ, cost))
    (hstep : step cost (op, arg) { stateZ with executionEnv.depth := state.executionEnv.depth }
      = .ok state') :
    memoryCost ((state'.machineState.H_return.size + 31) / 32) ≤ memoryGas state := by
  have hs := step_return_output_words hop hstep
  have hsame := Z_stack_active_eq hZ
  have he : memoryExpansionWords { stateZ with executionEnv.depth := state.executionEnv.depth } op =
      memoryExpansionWords state op := by
    simp only [memoryExpansionWords, hsame.1, hsame.2.1]
  rw [he] at hs
  have hn : (state'.machineState.H_return.size + 31) / 32 ≤ memoryExpansionWords state op := by
    omega
  have hm := memoryCost_mono hn
  rw [memoryCost_eq_Cₘ (memoryExpansionWords_lt_uint256_size state op)] at hm
  exact hm.trans ((Nat.le_add_right _ _).trans (memoryGas_after_Z hZ))

theorem Xstep_halt_output_memoryCost {validJumps : Array UInt256} {state state' : State}
    {cause : HaltCause} {out : ByteArray}
    (h : Xstep validJumps state = .ok (state', some (cause, out))) :
    memoryCost ((out.size + 31) / 32) ≤ memoryGas state := by
  unfold Xstep at h
  simp [bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i cost hZ
    split at h
    · contradiction
    · rename_i stepped hstep
      generalize hinstr :
        (decode state.executionEnv.code state.machineState.pc).getD (.STOP, none) = instr
        at hZ hstep h
      rcases instr with ⟨op, arg⟩
      cases op with
      | StopArith sop =>
        cases sop <;> simp at h
        rcases h with ⟨_, _, rfl⟩
        simp [memoryCost]
      | CompBit op => cases op <;> simp at h
      | Keccak op => cases op; simp at h
      | Env op => cases op <;> simp at h
      | Block op => cases op <;> simp at h
      | StackMemFlow op => cases op <;> simp at h
      | Push op => cases op <;> simp at h
      | Dup op => cases op <;> simp at h
      | Exchange op => cases op <;> simp at h
      | Log op => cases op <;> simp at h
      | System sop =>
        cases sop <;> simp at h
        · rcases h with ⟨_, _, rfl⟩
          exact return_output_memoryCost (Or.inl rfl) hZ hstep
        · rcases h with ⟨_, _, rfl⟩
          exact return_output_memoryCost (Or.inr rfl) hZ hstep
        · rcases h with ⟨_, _, rfl⟩
          simp [memoryCost]

end Benchmarks.Midnight

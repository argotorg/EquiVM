import Benchmarks.UniswapV4PoolManager.CalleeOperationGas
import Benchmarks.UniswapV4PoolManager.CalleeReturnGas

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

theorem stepReturn_outputFootprint {cost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step cost (.RETURN, arg) s = .ok s') :
    memoryFootprint s'.machineState.H_return ≤ memoryFootprint s'.machineState.memory := by
  rw [step.eq_1] at h
  simp only [binaryMachineStateOp, Id.run] at h
  split at h
  · rename_i rest off len hp
    simp only [Except.ok.injEq] at h
    subst s'
    exact memoryFootprint_readWithPadding s.machineState.memory off.toNat len.toNat
  · contradiction

theorem Xstep_success_nonzero_return {validJumps : Array UInt256} {s s' : State} {out : ByteArray}
    (hn : 0 < memoryFootprint out)
    (h : Xstep validJumps s = .ok (s', some (.success, out))) :
    ((decode s.executionEnv.code s.machineState.pc).getD (.STOP, none)).1 = .RETURN ∧
      memoryFootprint out ≤ memoryFootprint s'.machineState.memory := by
  unfold Xstep at h
  simp [bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i cost hZ
    split at h
    · contradiction
    · rename_i stepped hstep
      generalize hinstr : (decode s.executionEnv.code s.machineState.pc).getD (.STOP, none) = instr at hZ hstep h ⊢
      rcases instr with ⟨op, arg⟩
      cases op with
      | StopArith sop =>
        cases sop <;> simp at h
        rcases h with ⟨rfl, rfl⟩
        rw [memoryFootprint_of_zero MemoryZero.empty] at hn
        omega
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
        · rcases h with ⟨rfl, rfl⟩
          exact ⟨rfl, stepReturn_outputFootprint hstep⟩
        · rcases h with ⟨rfl, rfl⟩
          rw [memoryFootprint_of_zero MemoryZero.empty] at hn
          omega

theorem X_success_returnWork {fuel : Nat} {validJumps : Array UInt256}
    {s s' : State} {out : ByteArray} (hn : 0 < memoryFootprint out)
    (h : X fuel validJumps s = .ok (.success s' out)) :
    Cₘ s'.machineState.activeWords+s'.machineState.gasAvailable.toNat+memoryFootprint out+4 ≤
      executionPotential s := by
  induction fuel generalizing s with
  | zero => simp [X] at h
  | succ fuel ih =>
    unfold X at h
    simp only [bind, Except.bind] at h
    cases hstep : Xstep validJumps s with
    | error e => simp [hstep] at h
    | ok res =>
      rcases res with ⟨state₁, ret⟩
      simp only [hstep] at h
      cases ret with
      | none =>
        have hp := Xstep_executionPotential_le hstep
        exact (ih h).trans hp
      | some halted =>
        rcases halted with ⟨cause, haltOut⟩
        cases cause <;> simp at h
        rcases h with ⟨rfl, rfl⟩
        obtain ⟨hr, hf⟩ := Xstep_success_nonzero_return hn hstep
        have hp := Xstep_executionPotential_return hstep
        rw [hr, if_pos rfl] at hp
        dsimp only [executionPotential, operationPotential] at hp ⊢
        omega

-- LIBRARY CANDIDATE: nonzero return bytes require paid memory, stack operands, and memory writes.
theorem Xi_success_returnWork {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {res : AccountMap × UInt256 × Substate} {out : ByteArray} (hn : 0 < memoryFootprint out)
    (h : Ξ σ σ₀ g A I = .ok (.success res out)) :
    Cₘ (UInt256.ofNat ((out.size+31)/32))+memoryFootprint out+4+res.2.1.toNat ≤ g.toNat := by
  unfold Ξ at h
  simp [bind, Except.bind] at h
  cases hx : X (g.toNat+1) (D_J I.code 0)
      { (default : State) with
        accountMap := σ, σ₀ := σ₀, executionEnv := I, substate := A,
        machineState.gasAvailable := .ofUInt256 g } with
  | error e => simp [hx] at h
  | ok result =>
    cases result with
    | revert gas data => simp [hx] at h
    | success state' data =>
      simp only [hx] at h
      rcases h with ⟨rfl, rfl⟩
      have hp := X_success_returnWork hn hx
      have hw := X_success_outputWords hx
      have hm := Cₘ_monotone_of_lt (show (out.size+31)/32 ≤ state'.machineState.activeWords.toNat by omega)
        state'.machineState.activeWords.val.isLt
      rw [u256_ofNat_toNat] at hm
      have hz := memoryFootprint_of_zero MemoryZero.empty
      have hb : Cₘ state'.machineState.activeWords+state'.machineState.gasAvailable.toNat+memoryFootprint out+4 ≤ g.toNat := by
        simpa only [executionPotential, operationPotential, Cₘ, GasConstants.Gmemory, Cₘ.QuadraticCeofficient,
          show (default : State).machineState.activeWords.toNat = 0 from rfl,
          show (default : State).machineState.stack.length = 0 from rfl,
          show (default : State).machineState.memory = ByteArray.empty from rfl, hz,
          Nat.mul_zero, Nat.zero_mul, Nat.zero_add, Nat.add_zero, Nat.zero_div] using hp
      change Cₘ (UInt256.ofNat ((out.size+31)/32))+memoryFootprint out+4+
        state'.machineState.gasAvailable.toNat ≤ g.toNat
      omega

end Benchmarks.UniswapV4PoolManager

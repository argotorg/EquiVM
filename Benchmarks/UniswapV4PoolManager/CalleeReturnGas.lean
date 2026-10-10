import Benchmarks.UniswapV4PoolManager.CalleeMemoryGas
import Benchmarks.UniswapV4PoolManager.ThetaSuccess

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: the returned byte span fits the active memory charged by RETURN.
theorem stepReturn_outputWords {cost : Nat} {arg : Option (UInt256 × Nat)} {state state' : State}
    (h : step cost (.RETURN, arg) state = .ok state') :
    state'.machineState.H_return.size ≤ 32*state'.machineState.activeWords.toNat := by
  unfold step at h
  simp [binaryMachineStateOp] at h
  cases hpop : state.machineState.stack.pop2 with
  | none => simp [hpop] at h
  | some popped =>
    rcases popped with ⟨stack, offset, len⟩
    simp [hpop, MachineState.evmReturn, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] at h
    injection h with hs
    subst state'
    change (state.machineState.memory.readWithPadding offset.toNat len.toNat).size ≤
      32*(M state.machineState.activeWords offset len).toNat
    rw [memoryWords_toNat]
    exact MachineState.evmReturn_H_return_size_le_words_mul state.machineState offset len

theorem Xstep_success_outputWords {validJumps : Array UInt256} {state state' : State} {out : ByteArray}
    (h : Xstep validJumps state = .ok (state', some (.success, out))) :
    out.size ≤ 32*state'.machineState.activeWords.toNat := by
  unfold Xstep at h
  simp [bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i cost hZ
    split at h
    · contradiction
    · rename_i stepped hstep
      generalize hinstr :
        (decode state.executionEnv.code state.machineState.pc).getD (.STOP, none) = instr at hZ hstep h
      rcases instr with ⟨op, arg⟩
      cases op with
      | StopArith sop =>
        cases sop <;> simp at h
        rcases h with ⟨rfl, rfl⟩
        simp
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
          exact stepReturn_outputWords hstep
        · rcases h with ⟨rfl, rfl⟩
          simp

theorem X_success_outputWords {fuel : Nat} {validJumps : Array UInt256}
    {state state' : State} {out : ByteArray}
    (h : X fuel validJumps state = .ok (.success state' out)) :
    out.size ≤ 32*state'.machineState.activeWords.toNat := by
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
      cases ret with
      | none => exact ih h
      | some halted =>
        rcases halted with ⟨cause, haltOut⟩
        cases cause <;> simp at h
        rcases h with ⟨rfl, rfl⟩
        exact Xstep_success_outputWords hstep

-- LIBRARY CANDIDATE: a fresh EVM callee pays the memory cost of every returned byte.
theorem Xi_success_returnMemoryCost {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {res : AccountMap × UInt256 × Substate} {out : ByteArray}
    (h : Ξ σ σ₀ g A I = .ok (.success res out)) :
    Cₘ (UInt256.ofNat ((out.size+31)/32))+res.2.1.toNat ≤ g.toNat := by
  unfold Ξ at h
  simp [bind, Except.bind] at h
  cases hx : X (g.toNat+1) (D_J I.code 0)
      { (default : State) with
        accountMap := σ, σ₀ := σ₀, executionEnv := I, substate := A,
        machineState.gasAvailable := .ofUInt256 g } with
  | error e => simp [hx] at h
  | ok xres =>
    cases xres with
    | revert g' xiOut => simp [hx] at h
    | success state' xiOut =>
      have hpaid := X_success_memoryCostGas_le hx
      have hwords := X_success_outputWords hx
      have hw : (xiOut.size+31)/32 ≤ state'.machineState.activeWords.toNat := by omega
      have hm := Cₘ_monotone_of_lt hw state'.machineState.activeWords.val.isLt
      rw [u256_ofNat_toNat] at hm
      have hp : Cₘ state'.machineState.activeWords+state'.machineState.gasAvailable.toNat ≤ g.toNat := by
        simpa only [Cₘ, GasConstants.Gmemory, Cₘ.QuadraticCeofficient,
          show (default : State).machineState.activeWords.toNat = 0 from rfl,
          Nat.mul_zero, Nat.zero_mul, Nat.zero_add, Nat.add_zero, Nat.zero_div] using hpaid
      simp only [hx] at h
      rcases h with ⟨rfl, rfl⟩
      exact (Nat.add_le_add_right hm _).trans hp

theorem thetaCode_success_returnMemoryCost
    {σ σ₀ : AccountMap} {A : Substate} {s o r : AccountAddress}
    {code d : ByteArray} {g p v v' : UInt256} {e : Fin 1025} {H : BlockHeader}
    {blob : List ByteArray} {blocks : ProcessedBlocks} {perm : Bool}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {out : ByteArray}
    (h : Ethereum.EVM.Θ σ σ₀ A s o r (.Code code) g p v v' d e H blob blocks perm =
      (σ', g', A', true, out)) :
    Cₘ (UInt256.ofNat ((out.size+31)/32))+g'.toNat ≤ g.toNat := by
  obtain ⟨inputAccounts, I, accounts, substate, hx⟩ := thetaCode_success_Xi h
  exact Xi_success_returnMemoryCost hx

end Benchmarks.UniswapV4PoolManager

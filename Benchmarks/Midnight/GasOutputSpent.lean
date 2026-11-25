import Benchmarks.Midnight.GasOutput
import Benchmarks.Midnight.PrecompileOutput

variable {fork : Ethereum.Fork}

/-! Output memory is paid for by consumed gas, even when unused gas is returned to a caller. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: keep the final gas in the quantitative output-memory bound.
theorem return_output_memoryCost_remaining {validJumps : Array UInt256} {op : Operation}
    {state stateZ state' : State} {cost : Nat} {arg : Option (UInt256 × Nat)}
    (hop : op = .RETURN ∨ op = .REVERT)
    (hZ : Z fork validJumps op state = .ok (stateZ, cost))
    (hstep : step fork cost (op, arg) { stateZ with executionEnv.depth := state.executionEnv.depth }
      = .ok state') :
    memoryCost ((state'.machineState.H_return.size + 31) / 32) +
      state'.machineState.gasAvailable.toNat ≤ memoryGas state := by
  have hs := step_return_output_words hop hstep
  have hsame := Z_stack_active_eq hZ
  have he : memoryExpansionWords { stateZ with executionEnv.depth := state.executionEnv.depth } op =
      memoryExpansionWords state op := by
    simp only [memoryExpansionWords, hsame.1, hsame.2.1]
  rw [he] at hs
  have hm := memoryCost_mono
    (show (state'.machineState.H_return.size + 31) / 32 ≤ memoryExpansionWords state op by omega)
  rw [memoryCost_eq_Cₘ (memoryExpansionWords_lt_uint256_size state op)] at hm
  have hgas := step_gas_le hstep
  change state'.machineState.gasAvailable.toNat ≤ stateZ.machineState.gasAvailable.toNat at hgas
  exact (Nat.add_le_add hm hgas).trans (memoryGas_after_Z hZ)

theorem Xstep_halt_output_memoryCost_remaining {validJumps : Array UInt256}
    {state state' : State} {cause : HaltCause} {out : ByteArray}
    (h : Xstep fork validJumps state = .ok (state', some (cause, out))) :
    memoryCost ((out.size + 31) / 32) + state'.machineState.gasAvailable.toNat ≤
      memoryGas state := by
  have hg := Xstep_memoryGas_le h
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
        simp only [ByteArray.size_empty, Nat.zero_add, Nat.reduceDiv, memoryCost,
          Nat.mul_zero, Nat.zero_div, Nat.add_zero]
        unfold memoryGas at hg ⊢
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
        · rcases h with ⟨rfl, _, rfl⟩
          exact return_output_memoryCost_remaining (Or.inl rfl) hZ hstep
        · rcases h with ⟨rfl, _, rfl⟩
          exact return_output_memoryCost_remaining (Or.inr rfl) hZ hstep
        · rcases h with ⟨_, _, rfl⟩
          simp only [ByteArray.size_empty, Nat.zero_add, Nat.reduceDiv, memoryCost,
            Nat.mul_zero, Nat.zero_div, Nat.add_zero]
          unfold memoryGas at hg ⊢
          omega

def executionRemainingGas {α : Type} (gas : α → Nat) : ExecutionResult α → Nat
  | .success state _ => gas state
  | .revert g _ => g.toNat

theorem X_output_memoryCost_remaining {fuel : Nat} {validJumps : Array UInt256}
    {state : State} {res : ExecutionResult State}
    (h : X fork fuel validJumps state = .ok res) :
    memoryCost (((executionOutput res).size + 31) / 32) +
      executionRemainingGas (fun s ↦ s.machineState.gasAvailable.toNat) res ≤ memoryGas state := by
  induction fuel generalizing state with
  | zero => simp [X] at h
  | succ fuel ih =>
    unfold X at h
    simp [bind, Except.bind] at h
    cases hstep : Xstep fork validJumps state with
    | error e => simp [hstep] at h
    | ok stepResult =>
      rcases stepResult with ⟨state₁, ret⟩
      simp [hstep] at h
      cases ret with
      | none =>
        have hb := Xstep_memoryGas_le hstep
        exact (ih h).trans hb
      | some halted =>
        rcases halted with ⟨cause, haltOut⟩
        cases cause <;> simp at h <;> subst res <;>
          exact Xstep_halt_output_memoryCost_remaining hstep

theorem Xi_output_memoryCost_remaining {σ σ₀ : AccountMap} {g : UInt256} {A : Substate}
    {I : ExecutionEnv} {res : ExecutionResult (AccountMap × UInt256 × Substate)}
    (h : Ξ fork σ σ₀ g A I = .ok res) :
    memoryCost (((executionOutput res).size + 31) / 32) +
      executionRemainingGas (fun r ↦ r.2.1.toNat) res ≤ g.toNat := by
  unfold Ξ at h
  simp [bind, Except.bind] at h
  cases hx : X fork (g.toNat + 1) (D_J I.code 0)
      { (default : State) with
        accountMap := σ, σ₀ := σ₀, executionEnv := I, substate := A,
        machineState.gasAvailable := .ofUInt256 g } with
  | error e => simp [hx] at h
  | ok xres =>
    have hout := X_output_memoryCost_remaining hx
    have hbudget : memoryGas
        { (default : State) with
          accountMap := σ, σ₀ := σ₀, executionEnv := I, substate := A,
          machineState.gasAvailable := .ofUInt256 g } = g.toNat := by
      have h0 : (default : State).machineState.activeWords.toNat = 0 := rfl
      simp [memoryGas, Cₘ, GasConstants.Gmemory, Cₘ.QuadraticCeofficient, h0]
    rw [hbudget] at hout
    cases xres <;> simp [hx] at h <;> subst res <;> exact hout

theorem Xi_tuple_output_memoryCost_remaining
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    let result := match Ξ fork σ σ₀ g A I with
      | .error _ => (∅, (⟨0⟩ : UInt256), A, ByteArray.empty)
      | .ok (.revert g' out) => (∅, g', A, out)
      | .ok (.success (σ', g', A') out) => (σ', g', A', out)
    memoryCost ((result.2.2.2.size + 31) / 32) + result.2.1.toNat ≤ g.toNat := by
  cases hxi : Ξ fork σ σ₀ g A I with
  | error err => simp [memoryCost]
  | ok xres =>
    cases xres with
    | revert g' out => exact Xi_output_memoryCost_remaining hxi
    | success res out =>
      rcases res with ⟨σ', g', A'⟩
      exact Xi_output_memoryCost_remaining hxi

theorem theta_code_output_memoryCost_remaining
    (fork : Fork) (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress)
    (code d : ByteArray) (g p v v' : UInt256) (e : Fin 1025) (H : BlockHeader)
    (blobVersionedHashes : List ByteArray) (blocks : ProcessedBlocks) (w : Bool) :
    let result := Θ fork σ σ₀ A s o r (.Code code) g p v v' d e H blobVersionedHashes blocks w
    memoryCost ((result.2.2.2.2.size + 31) / 32) + result.2.1.toNat ≤ g.toNat := by
  let σ'₁ := match σ.get? r with
    | none => if v != UInt256.ofNat 0 then
        σ.insert r { (default : Account) with balance := v } else σ
    | some acc => σ.insert r { acc with balance := acc.balance + v }
  let σ₁ := match σ'₁.get? s with
    | none => σ'₁
    | some acc => σ'₁.insert s { acc with balance := acc.balance - v }
  let I : ExecutionEnv :=
    { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d,
      source := s, weiValue := v', depth := e, perm := w, code := code,
      header := H, blobVersionedHashes := blobVersionedHashes, blocks := blocks}
  unfold Θ
  simpa only [σ'₁, σ₁, I] using Xi_tuple_output_memoryCost_remaining σ₁ σ₀ g A I

theorem theta_output_memoryCost_remaining_or_small
    (fork : Fork) (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress)
    (todo : ToExecute) (d : ByteArray) (g p v v' : UInt256) (e : Fin 1025) (H : BlockHeader)
    (blobVersionedHashes : List ByteArray) (blocks : ProcessedBlocks) (w : Bool)
    (hosaka : fork ≥ .osaka) :
    let result := Θ fork σ σ₀ A s o r todo g p v v' d e H blobVersionedHashes blocks w
    result.2.2.2.2.size ≤ max 1024 d.size ∨
      memoryCost ((result.2.2.2.2.size + 31) / 32) + result.2.1.toNat ≤ g.toNat := by
  cases todo with
  | Code code =>
    exact Or.inr (theta_code_output_memoryCost_remaining fork σ σ₀ A s o r code d g p v v' e H
      blobVersionedHashes blocks w)
  | Precompiled pc =>
    exact Or.inl (theta_precompiled_output_size_le_1024_or_calldata fork σ σ₀ A s o r pc
      d g p v v' e H blobVersionedHashes blocks w hosaka)

end Benchmarks.Midnight

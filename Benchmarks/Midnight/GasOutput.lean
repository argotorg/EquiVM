import Benchmarks.Midnight.GasMemory

variable {fork : Ethereum.Fork}

/-! A code execution's output memory cost is bounded by its initial gas. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: output-size bounds parameterized by actual execution gas.
def executionOutput {α : Type} : ExecutionResult α → ByteArray
  | .success _ out => out
  | .revert _ out => out

theorem X_output_memoryCost {fuel : Nat} {validJumps : Array UInt256}
    {state : State} {res : ExecutionResult State}
    (h : X fork fuel validJumps state = .ok res) :
    memoryCost (((executionOutput res).size + 31) / 32) ≤ memoryGas state := by
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
          exact Xstep_halt_output_memoryCost hstep

theorem Xi_output_memoryCost {σ σ₀ : AccountMap} {g : UInt256} {A : Substate}
    {I : ExecutionEnv} {res : ExecutionResult (AccountMap × UInt256 × Substate)}
    (h : Ξ fork σ σ₀ g A I = .ok res) :
    memoryCost (((executionOutput res).size + 31) / 32) ≤ g.toNat := by
  unfold Ξ at h
  simp [bind, Except.bind] at h
  cases hx : X fork (g.toNat + 1) (D_J I.code 0)
      { (default : State) with
        accountMap := σ, σ₀ := σ₀, executionEnv := I, substate := A,
        machineState.gasAvailable := .ofUInt256 g } with
  | error e => simp [hx] at h
  | ok xres =>
    have hout := X_output_memoryCost hx
    have hbudget : memoryGas
        { (default : State) with
          accountMap := σ, σ₀ := σ₀, executionEnv := I, substate := A,
          machineState.gasAvailable := .ofUInt256 g } = g.toNat := by
      have h0 : (default : State).machineState.activeWords.toNat = 0 := rfl
      simp [memoryGas, Cₘ, GasConstants.Gmemory, Cₘ.QuadraticCeofficient, h0]
    rw [hbudget] at hout
    cases xres <;> simp [hx] at h <;> subst res <;> exact hout

theorem Xi_tuple_output_memoryCost
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    memoryCost (((match Ξ fork σ σ₀ g A I with
      | .error _ => (∅, (⟨0⟩ : UInt256), A, ByteArray.empty)
      | .ok (.revert g' out) => (∅, g', A, out)
      | .ok (.success (σ', g', A') out) => (σ', g', A', out)).2.2.2.size + 31) / 32)
      ≤ g.toNat := by
  cases hxi : Ξ fork σ σ₀ g A I with
  | error err => simp [memoryCost]
  | ok xres =>
    cases xres with
    | revert g' out => exact Xi_output_memoryCost hxi
    | success res out =>
      rcases res with ⟨σ', g', A'⟩
      exact Xi_output_memoryCost hxi

theorem theta_code_output_memoryCost
    (fork : Fork) (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress)
    (code d : ByteArray) (g p v v' : UInt256) (e : Fin 1025) (H : BlockHeader)
    (blobVersionedHashes : List ByteArray) (blocks : ProcessedBlocks) (w : Bool) :
    memoryCost (((Θ fork σ σ₀ A s o r (.Code code) g p v v' d e H
      blobVersionedHashes blocks w).2.2.2.2.size + 31) / 32) ≤ g.toNat := by
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
  simpa only [σ'₁, σ₁, I] using Xi_tuple_output_memoryCost σ₁ σ₀ g A I

end Benchmarks.Midnight

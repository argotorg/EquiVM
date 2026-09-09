import Reasoning.Reach

open Ethereum Ethereum.EVM

namespace Auction.ReturnDataProperties

-- GENERALIZES Ethereum.EVM.Xstep_halt_output_size_le_maxReturnDataSizeByGas:
-- propagate any property of empty output and memory reads through interpreted code.
variable {P : ByteArray → Prop}

theorem step_halt_property
    (hread : ∀ (mem : ByteArray) (off len : Nat), P (mem.readWithPadding off len))
    {cost : Nat} {arg : Option (UInt256 × Nat)} {state state' : State} {op : Operation}
    (hop : op = .RETURN ∨ op = .REVERT)
    (h : step cost (op, arg) state = .ok state') : P state'.machineState.H_return := by
  rcases hop with rfl | rfl
  all_goals
    unfold step at h
    simp [binaryMachineStateOp] at h
    cases hpop : state.machineState.stack.pop2 with
    | none => simp [hpop] at h
    | some popped =>
        rcases popped with ⟨stack, offset, len⟩
        simp [hpop, MachineState.evmRevert, MachineState.evmReturn,
          Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
        injection h with hstate
        subst state'
        exact hread state.machineState.memory offset.toNat len.toNat

theorem Xstep_halt_property (hempty : P ByteArray.empty)
    (hread : ∀ (mem : ByteArray) (off len : Nat), P (mem.readWithPadding off len))
    {validJumps : Array UInt256} {state state' : State} {cause : HaltCause} {out : ByteArray}
    (h : Xstep validJumps state = .ok (state', some (cause, out))) : P out := by
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
        at hstep h
      rcases instr with ⟨op, arg⟩
      cases op with
      | StopArith sop =>
          cases sop <;> simp at h
          rcases h with ⟨_, _, hout⟩
          subst out
          exact hempty
      | CompBit op => cases op <;> simp at h
      | Keccak op => cases op <;> simp at h
      | Env op => cases op <;> simp at h
      | Block op => cases op <;> simp at h
      | StackMemFlow op => cases op <;> simp at h
      | Push op => cases op <;> simp at h
      | Dup op => cases op <;> simp at h
      | Exchange op => cases op <;> simp at h
      | Log op => cases op <;> simp at h
      | System sop =>
          cases sop <;> simp at h
          · rcases h with ⟨_, _, hout⟩
            subst out
            exact step_halt_property hread (Or.inl rfl) hstep
          · rcases h with ⟨_, _, hout⟩
            subst out
            exact step_halt_property hread (Or.inr rfl) hstep
          · rcases h with ⟨_, _, hout⟩
            subst out
            exact hempty

def resultProperty {α : Type} (P : ByteArray → Prop) :
    Except ExecutionException (ExecutionResult α) → Prop
  | .error _ => True
  | .ok (.success _ out) => P out
  | .ok (.revert _ out) => P out

theorem X_property (hempty : P ByteArray.empty)
    (hread : ∀ (mem : ByteArray) (off len : Nat), P (mem.readWithPadding off len))
    (fuel : Nat) (validJumps : Array UInt256) (state : State) :
    resultProperty P (X fuel validJumps state) := by
  induction fuel generalizing state with
  | zero => simp [X, resultProperty]
  | succ fuel ih =>
      unfold X
      cases hstep : Xstep validJumps state with
      | error e => simp [hstep, bind, Except.bind, resultProperty]
      | ok res =>
          rcases res with ⟨next, ret⟩
          cases ret with
          | none =>
              simpa [hstep, bind, Except.bind] using
                (ih { next with executionEnv.depth := state.executionEnv.depth })
          | some halted =>
              rcases halted with ⟨cause, out⟩
              have hout := Xstep_halt_property hempty hread hstep
              cases cause <;> simpa [hstep, bind, Except.bind, resultProperty] using hout

theorem Xi_property (hempty : P ByteArray.empty)
    (hread : ∀ (mem : ByteArray) (off len : Nat), P (mem.readWithPadding off len))
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader) (bl : ProcessedBlocks)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    resultProperty P (Ξ cA gh bl σ σ₀ g A I) := by
  let fresh : State :=
    { (default : State) with
      accountMap := σ, σ₀ := σ₀, executionEnv := I, substate := A, createdAccounts := cA,
      machineState.gasAvailable := .ofUInt256 g, blocks := bl, genesisBlockHeader := gh }
  have hx := X_property hempty hread (g.toNat + 1) (D_J I.code 0) fresh
  unfold Ξ
  change resultProperty P (do
    let result ← X (g.toNat + 1) (D_J I.code 0) fresh
    match result with
    | .success s out => pure (.success
        (s.createdAccounts, s.accountMap, s.machineState.gasAvailable.toUInt256, s.substate) out)
    | .revert g' out => pure (.revert g' out))
  cases hres : X (g.toNat + 1) (D_J I.code 0) fresh with
  | error e => simp [hres, resultProperty, bind, Except.bind]
  | ok result =>
      cases result <;> simpa [hres, resultProperty, bind, Except.bind] using hx

theorem Xi_match_property (hempty : P ByteArray.empty)
    (hread : ∀ (mem : ByteArray) (off len : Nat), P (mem.readWithPadding off len))
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader) (bl : ProcessedBlocks)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    P (match Ξ cA gh bl σ σ₀ g A I with
      | .error _ => (cA, ∅, (⟨0⟩ : UInt256), A, ByteArray.empty)
      | .ok (.revert g' out) => (cA, ∅, g', A, out)
      | .ok (.success (cA', σ', g', A') out) => (cA', σ', g', A', out)).2.2.2.2 := by
  have hx := Xi_property hempty hread cA gh bl σ σ₀ g A I
  cases hres : Ξ cA gh bl σ σ₀ g A I with
  | error e => exact hempty
  | ok result =>
      cases result with
      | revert g' out => simpa [hres, resultProperty] using hx
      | success res out =>
          rcases res with ⟨cA', σ', g', A'⟩
          simpa [hres, resultProperty] using hx

theorem theta_code_property (hempty : P ByteArray.empty)
    (hread : ∀ (mem : ByteArray) (off len : Nat), P (mem.readWithPadding off len))
    (blob : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (bl : ProcessedBlocks) (σ σ₀ : AccountMap) (A : Substate)
    (s o r : AccountAddress) (code d : ByteArray) (g p v v' : UInt256)
    (e : Fin 1025) (H : BlockHeader) (w : Bool) :
    P (Θ blob cA gh bl σ σ₀ A s o r (.Code code) g p v v' d e H w).2.2.2.2.2 := by
  unfold Θ
  simp only
  exact Xi_match_property hempty hread _ _ _ _ _ _ _ _

theorem readWithPadding_size_lt_2pow64 (mem : ByteArray) (off len : Nat) :
    (mem.readWithPadding off len).size < 2 ^ 64 := by
  by_cases hlen : 2 ^ 64 ≤ len
  · norm_num at hlen
    simp [ByteArray.readWithPadding, hlen, default, Inhabited.default]
  · exact lt_of_le_of_lt (ByteArray.readWithPadding_size_le mem off len) (by omega)

theorem theta_code_size_lt_2pow64
    (blob : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (bl : ProcessedBlocks) (σ σ₀ : AccountMap) (A : Substate)
    (s o r : AccountAddress) (code d : ByteArray) (g p v v' : UInt256)
    (e : Fin 1025) (H : BlockHeader) (w : Bool) :
    (Θ blob cA gh bl σ σ₀ A s o r (.Code code) g p v v' d e H w).2.2.2.2.2.size <
      2 ^ 64 :=
  theta_code_property (P := fun out ↦ out.size < 2 ^ 64)
    (by decide) readWithPadding_size_lt_2pow64
    blob cA gh bl σ σ₀ A s o r code d g p v v' e H w

end Auction.ReturnDataProperties

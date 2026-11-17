import Reasoning.Stepping
import Stele.Semantics.Calls
import Ethereum.Theory.GasLemmas
import Ethereum.Theory.PrecompileLemmas

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 5000

private theorem emptyStackHaltIsStop {validJumps : Array UInt256} {state state' : State}
    {cause : HaltCause} {out : ByteArray} (hs : state.machineState.stack = [])
    (h : Xstep validJumps state = .ok (state', some (cause, out))) :
    ((decode state.executionEnv.code state.machineState.pc).getD (.STOP, none)).1 =
      .STOP := by
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
        at hZ hstep h ⊢
      rcases instr with ⟨op, arg⟩
      cases op with
      | StopArith op => cases op <;> simp_all
      | CompBit op => cases op <;> simp at h
      | Keccak op => cases op; simp at h
      | Env op => cases op <;> simp at h
      | Block op => cases op <;> simp at h
      | StackMemFlow op => cases op <;> simp at h
      | Push op => cases op <;> simp at h
      | Dup op => cases op <;> simp at h
      | Exchange op => cases op <;> simp at h
      | Log op => cases op <;> simp at h
      | System op =>
        cases op <;> simp at h <;> simp [Z, δ, hs] at hZ

private theorem expmodRequiredGas_positive (fork : Fork) (data : ByteArray) {gas : Nat}
    (h : expmodRequiredGas fork data = some gas) : 0 < gas := by
  unfold expmodRequiredGas at h
  split_ifs at h <;> simp_all <;> omega

private theorem xiZeroGasFailure (σ σ₀ : AccountMap) (A : Substate) (I : ExecutionEnv)
    (hn : ((decode I.code ⟨0⟩).getD (.STOP, none)).1 ≠ .STOP) :
    (match Ξ σ σ₀ ⟨0⟩ A I with
      | .error _ => (∅, (⟨0⟩ : UInt256), A, ByteArray.empty)
      | .ok (.revert g' out) => (∅, g', A, out)
      | .ok (.success (σ', g', A') out) => (σ', g', A', out)).1 = ∅ := by
  unfold Ξ
  simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.zero_add, X, bind, Except.bind]
  generalize hstep : Xstep (D_J I.code 0) _ = stepResult
  cases stepResult with
  | error _ => rfl
  | ok pair =>
    rcases pair with ⟨state, ret⟩
    cases ret with
    | none => rfl
    | some pair =>
      rcases pair with ⟨cause, out⟩
      exact False.elim (hn (emptyStackHaltIsStop rfl hstep))

private theorem stopDefaultStep {state : State} {jumps : Array UInt256}
    (hs : state.machineState.stack = [])
    (hd : ((decode state.executionEnv.code state.machineState.pc).getD (.STOP, none)).1 =
      .STOP) :
    Xstep jumps state = .ok (stStop state, some (.success, ByteArray.empty)) := by
  generalize hi : (decode state.executionEnv.code state.machineState.pc).getD (.STOP, none) =
    instr at hd
  rcases instr with ⟨op, arg⟩
  change op = .STOP at hd
  subst op
  simp [Xstep, hi, Z, δ, hs, memoryExpansionCost, memoryExpansionCost.μᵢ', C',
    InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
    InstructionGasGroups.Wzero, GasConstants.Gzero,
    α, Operation.isCreate, bind, Except.bind, step, MachineState.setReturnData, stStop]

private theorem xiStopOutput (σ σ₀ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv)
    (hd : ((decode I.code ⟨0⟩).getD (.STOP, none)).1 = .STOP) :
    (match Ξ σ σ₀ g A I with
      | .error _ => (∅, (⟨0⟩ : UInt256), A, ByteArray.empty)
      | .ok (.revert g' out) => (∅, g', A, out)
      | .ok (.success (σ', g', A') out) => (σ', g', A', out)).2.2.2 = .empty := by
  unfold Ξ
  dsimp only
  rw [X, stopDefaultStep rfl hd]
  rfl

set_option maxRecDepth 65536 in
private theorem precompileZeroGasFailure (pc : AccountAddress) (σ : AccountMap) (A : Substate)
    (I : ExecutionEnv) (hinput : I.calldata.size ≠ 213) :
    (Ξ_PRECOMPILE pc σ ⟨0⟩ A I).1 = ∅ := by
  apply Ξ_PRECOMPILE_induction (P := fun result => result.1 = ∅)
  · simp [Ξ_ECREC]
  · simp [Ξ_SHA256]
  · simp [Ξ_RIP160]
  · simp [Ξ_ID]
  · unfold Ξ_EXPMOD
    dsimp only
    cases hg : expmodRequiredGas I.fork I.calldata with
    | none => rfl
    | some gas =>
      have hpos := expmodRequiredGas_positive I.fork I.calldata hg
      simp [hpos]
  · simp [Ξ_BN_ADD]
  · simp [Ξ_BN_MUL]
  · simp [Ξ_SNARKV]
  · have hb : Ethereum.Crypto.BLAKE2F.blake2f I.calldata = none := by
      unfold Ethereum.Crypto.BLAKE2F.blake2f; simp [hinput]
    simp [Ξ_BLAKE2_F, BLAKE2_F, hb, dbgTrace]
  · simp [Ξ_PointEval]
  · intro op
    simp [precompile_BLS12_381_zero_gas]
  · simp [Ξ_P256VERIFY]
  · rfl

private theorem thetaZeroGasFailureOfNonempty (fork : Fork) (σ σ₀ : AccountMap) (A A₀ : Substate)
    (s o r : AccountAddress) (c : ToExecute) (g p v v' : UInt256) (d : ByteArray)
    (e : Fin 1025) (H : BlockHeader) (hashes : List ByteArray) (blocks : ProcessedBlocks)
    (perm : Bool) (hinput : d.size ≠ 213)
    (hout : (Θ fork σ σ₀ A s o r c g p v v' d e H hashes blocks perm).2.2.2.2 ≠ .empty) :
    (Θ fork σ σ₀ A₀ s o r c ⟨0⟩ p v v' d e H hashes blocks perm).2.2.2.1 = false := by
  cases c with
  | Code code =>
    have hn : ((decode code ⟨0⟩).getD (.STOP, none)).1 ≠ .STOP := by
      intro hd
      apply hout
      unfold Θ
      dsimp only
      exact xiStopOutput _ σ₀ g A _ hd
    unfold Θ
    dsimp only
    apply if_pos
    apply Eq.trans (b := ((∅ : AccountMap) == ∅))
    · apply congrArg (fun m : AccountMap ↦ m == ∅)
      exact xiZeroGasFailure _ σ₀ A₀ _ hn
    · rfl
  | Precompiled pc =>
    unfold Θ
    dsimp only
    apply if_pos
    apply Eq.trans (b := ((∅ : AccountMap) == ∅))
    · apply congrArg (fun m : AccountMap ↦ m == ∅)
      exact precompileZeroGasFailure pc _ A₀ _ (by simpa using hinput)
    · rfl

/-- A call that can return nonempty data also admits a failing zero-gas call.
The input-size condition excludes the zero-round BLAKE2 precompile exception. -/
theorem callNonemptyCanReject {evm : State} {target : EVM.Address} {value : Int}
    {data out : ByteArray} {z : Bool} {evm' : State} {perm : Bool}
    (hc : callViaEVM evm target value data (z, evm', out) perm)
    (hinput : data.size ≠ 213) (hout : out ≠ .empty) :
    ∃ evm'' out', callViaEVM evm target value data (false, evm'', out') perm := by
  cases hc with
  | callNotMade _ _ _ => exact False.elim (hout rfl)
  | callMade hw hr he hb hd =>
    rw [hw] at hr hb
    obtain ⟨gas, A, hr⟩ := hr
    let result := Θ evm.executionEnv.fork evm.accountMap evm.σ₀ default evm.executionEnv.codeOwner
      evm.executionEnv.sender target (toExecute evm.executionEnv.fork evm.accountMap target) ⟨0⟩
      (UInt256.ofNat evm.executionEnv.gasPrice) (EVM.wordOfInt value) (EVM.wordOfInt value) data
      (evm.executionEnv.depth + 1) evm.executionEnv.header evm.executionEnv.blobVersionedHashes
      evm.executionEnv.blocks (perm && evm.executionEnv.perm)
    have hz : result.2.2.2.1 = false :=
      thetaZeroGasFailureOfNonempty evm.executionEnv.fork _ _ A default _ _ _ _ gas _ _ _ _ _ _ _ _ _ hinput
        (by rw [← hr]; exact hout)
    refine ⟨{ evm with accountMap := result.1, substate := result.2.2.1 },
      result.2.2.2.2, ?_⟩
    rw [← hz]
    exact callViaEVM.callMade rfl ⟨⟨0⟩, default, rfl⟩ rfl hb hd

end Benchmarks.Safe.ViaIR

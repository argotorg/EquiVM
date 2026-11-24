import Benchmarks.Safe.ViaIR.ContractSignatureSource
import Ethereum.Theory.PrecompileLemmas

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

private theorem emptyStackHaltOutput {validJumps : Array UInt256} {state state' : State}
    {cause : HaltCause} {out : ByteArray} (hs : state.machineState.stack = [])
    (h : Xstep fork validJumps state = .ok (state', some (cause, out))) : out = .empty := by
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
      | StopArith op => cases op <;> simp at h; exact h.2.2.symm
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
        cases op <;> simp at h
        · simp [Z, δ, hs] at hZ
        · simp [Z, δ, hs] at hZ
        · exact h.2.2.symm

private theorem xiZeroGasOutput (σ σ₀ : AccountMap) (A : Substate) (I : ExecutionEnv) :
    (match Ξ fork σ σ₀ ⟨0⟩ A I with
      | .error _ => (∅, (⟨0⟩ : UInt256), A, ByteArray.empty)
      | .ok (.revert g' out) => (∅, g', A, out)
      | .ok (.success (σ', g', A') out) => (σ', g', A', out)).2.2.2 = .empty := by
  unfold Ξ
  simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.zero_add, X, bind, Except.bind]
  generalize hstep : Xstep fork (D_J I.code 0) _ = stepResult
  cases stepResult with
  | error _ => rfl
  | ok pair =>
    rcases pair with ⟨state, ret⟩
    cases ret with
    | none => rfl
    | some pair =>
      rcases pair with ⟨cause, out⟩
      have ho := emptyStackHaltOutput rfl hstep
      cases cause <;> simp only [ho]

private theorem precompileZeroGasOutput (pc : AccountAddress) (σ : AccountMap) (A : Substate)
    (I : ExecutionEnv) :
    (Ξ_PRECOMPILE fork pc σ ⟨0⟩ A I).2.2.2.size ≠ 32 := by
  apply Ξ_PRECOMPILE_induction fork (fun r ↦ r.2.2.2.size ≠ 32)
  · change (0 : Nat) ≠ 32; decide
  · simp [Ξ_SHA256]
  · simp [Ξ_RIP160]
  · simp [Ξ_ID]
  · unfold Ξ_EXPMOD
    dsimp only
    split
    · change (0 : Nat) ≠ 32; decide
    · rename_i gas hgas
      have hpos : 0 < gas := by
        unfold expmodRequiredGas at hgas
        dsimp only at hgas
        split at hgas
        · contradiction
        · split at hgas <;> simp only [Option.some.injEq] at hgas <;> subst gas <;> omega
      simp [hpos]
  · change (0 : Nat) ≠ 32; decide
  · change (0 : Nat) ≠ 32; decide
  · simp [Ξ_SNARKV]
  · unfold Ξ_BLAKE2_F
    dsimp only
    split
    · simp [dbgTrace]
    · cases hres : BLAKE2_F I.calldata with
      | error _ => simp [dbgTrace]
      | ok bytes => simp [BLAKE2_F_ok_output_size hres]
  · change (0 : Nat) ≠ 32; decide
  · intro op
    rw [precompile_BLS12_381_zero_gas]
    change (0 : Nat) ≠ 32; decide
  · change (0 : Nat) ≠ 32; decide
  · change (0 : Nat) ≠ 32; decide

private theorem thetaZeroGasOutput {fork : Ethereum.Fork} (σ σ₀ : AccountMap) (A : Substate) (s o r
  : AccountAddress)
    (c : ToExecute) (p v v' : UInt256) (d : ByteArray) (e : Fin 1025) (H : BlockHeader)
    (hashes : List ByteArray) (blocks : ProcessedBlocks) (perm : Bool) :
    (Θ fork σ σ₀ A s o r c ⟨0⟩ p v v' d e H hashes blocks perm).2.2.2.2.size ≠ 32 := by
  cases c with
  | Code code =>
    unfold Θ
    simp only
    change (match Ξ fork _ σ₀ ⟨0⟩ A _ with
      | .error _ => (∅, (⟨0⟩ : UInt256), A, ByteArray.empty)
      | .ok (.revert g' out) => (∅, g', A, out)
      | .ok (.success (σ', g', A') out) => (σ', g', A', out)).2.2.2.size ≠ 32
    rw [xiZeroGasOutput]
    decide
  | Precompiled pc =>
    unfold Θ
    simp only
    exact precompileZeroGasOutput pc _ A _

theorem contractSignatureCanReject (evm : EVM.State) (owner : EVM.Address)
    (hash : UInt256) (signature : ByteArray) :
    ∃ z evm' out, callViaEVM fork evm (EVM.address owner) 0
      (contractSignatureCallBytes hash signature) (z, evm', out) false ∧
      contractSignatureResult z out = false := by
  by_cases hd : evm.executionEnv.depth = 1024
  · exact ⟨false, _, ByteArray.empty,
      callViaEVM.callNotMade rfl rfl (fun hh ↦ hh.2 hd), rfl⟩
  · let result := Θ fork evm.accountMap evm.σ₀ default evm.executionEnv.codeOwner
      evm.executionEnv.sender (EVM.address owner)
      (toExecute fork evm.accountMap (EVM.address owner)) ⟨0⟩
      (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
      (contractSignatureCallBytes hash signature) (evm.executionEnv.depth + 1)
      evm.executionEnv.header evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks false
    refine ⟨result.2.2.2.1, { evm with accountMap := result.1, substate := result.2.2.1 },
      result.2.2.2.2, ?_, ?_⟩
    · apply callViaEVM.callMade (g' := result.2.1) wordOfInt_zero.symm
        ⟨⟨0⟩, default, ?_⟩ rfl (Fin.zero_le _) hd
      rfl
    · have hsize : result.2.2.2.2.size ≠ 32 := thetaZeroGasOutput _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      simp only [contractSignatureResult, hsize, decide_false, Bool.false_and, Bool.and_false]

private theorem precompileZeroGasEmpty (pc : AccountAddress) (σ : AccountMap) (A : Substate)
    (I : ExecutionEnv) (hinput : I.calldata.size ≠ 213) :
    (Ξ_PRECOMPILE fork pc σ ⟨0⟩ A I).2.2.2 = ByteArray.empty := by
  apply Ξ_PRECOMPILE_induction fork (fun r ↦ r.2.2.2 = ByteArray.empty)
  · rfl
  · simp [Ξ_SHA256]
  · simp [Ξ_RIP160]
  · simp [Ξ_ID]
  · unfold Ξ_EXPMOD
    dsimp only
    split
    · rfl
    · rename_i gas hgas
      have hpos : 0 < gas := by
        unfold expmodRequiredGas at hgas
        dsimp only at hgas
        split at hgas
        · contradiction
        · split at hgas <;> simp only [Option.some.injEq] at hgas <;> subst gas <;> omega
      simp [hpos]
  · rfl
  · rfl
  · simp [Ξ_SNARKV]
  · simp [Ξ_BLAKE2_F, BLAKE2_F, Crypto.BLAKE2F.blake2f, hinput, dbgTrace]
  · rfl
  · intro op
    rw [precompile_BLS12_381_zero_gas]
  · rfl
  · rfl

private theorem thetaZeroGasEmpty {fork : Ethereum.Fork} (σ σ₀ : AccountMap) (A : Substate) (s o r :
  AccountAddress)
    (c : ToExecute) (p v v' : UInt256) (d : ByteArray) (e : Fin 1025) (H : BlockHeader)
    (hashes : List ByteArray) (blocks : ProcessedBlocks) (perm : Bool) (hinput : d.size ≠ 213) :
    (Θ fork σ σ₀ A s o r c ⟨0⟩ p v v' d e H hashes blocks perm).2.2.2.2 = ByteArray.empty := by
  cases c with
  | Code code =>
    unfold Θ
    simp only
    exact xiZeroGasOutput _ σ₀ A _
  | Precompiled pc =>
    unfold Θ
    simp only
    exact precompileZeroGasEmpty pc _ A _ hinput

theorem callZeroGasEmptyOutput (evm : EVM.State) (target : EVM.Address) (data : ByteArray)
    (perm : Bool) (hinput : data.size ≠ 213) :
    ∃ z evm', callViaEVM fork evm target 0 data (z, evm', ByteArray.empty) perm := by
  by_cases hd : evm.executionEnv.depth = 1024
  · exact ⟨false, _, callViaEVM.callNotMade rfl rfl (fun hh ↦ hh.2 hd)⟩
  · let result := Θ fork evm.accountMap evm.σ₀ default evm.executionEnv.codeOwner
      evm.executionEnv.sender target (toExecute fork evm.accountMap target) ⟨0⟩
      (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩ data (evm.executionEnv.depth + 1)
      evm.executionEnv.header evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks
      (perm && evm.executionEnv.perm)
    have hout : result.2.2.2.2 = ByteArray.empty :=
      thetaZeroGasEmpty _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinput
    refine ⟨result.2.2.2.1, { evm with accountMap := result.1, substate := result.2.2.1 }, ?_⟩
    rw [← hout]
    apply callViaEVM.callMade (g' := result.2.1) wordOfInt_zero.symm
      ⟨⟨0⟩, default, ?_⟩ rfl (Fin.zero_le _) hd
    rfl

end Benchmarks.Safe.ViaIR

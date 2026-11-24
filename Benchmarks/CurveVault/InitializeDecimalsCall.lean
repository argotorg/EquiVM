import Benchmarks.CurveVault.MemoryActive
import Benchmarks.CurveVault.StaticWordCalls
import Benchmarks.CurveVault.UintReturnABI
import Benchmarks.CurveVault.RuntimeBlocks_002
import Benchmarks.CurveVault.RuntimeBlocks_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

abbrev vaultInitializeDecimalsStmt : Stmt := initializeTransition.body[3]!

theorem vaultInitializeDecimalsCall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {locals : Store} {gasArg target : UInt256}
    (hs : SourceState s0 I σ evm)
    (htarget : locals.get? "_borrowed_token_" = some (.address (AccountAddress.ofNat target.toNat)))
    (hcd : config.externalABI.encode? "decimals" [] = some (mem.readWithPadding 252 4))
    (hbuffer : 256 ≤ mem.size) (haw : aw.toNat ≤ 10) (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 247)
      (gasArg :: target :: ⟨252⟩ :: ⟨4⟩ :: ⟨224⟩ :: ⟨32⟩ :: target :: R) mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      (retWord out).toNat < 256 ∧ aw'.toNat ≤ 10 ∧
      ExecStmt fork config {contract := contract, locals := locals} evm vaultInitializeDecimalsStmt
        (.ok {contract := contract, locals := locals.insert "__c0" (.int (Int.ofNat (retWord out).toNat))} evm') ∧
      SourceState s0 I σ' evm' ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat 294) (retWord out :: ⟨32⟩ :: target :: R)
        ((retWord out).toByteArray.write 0 mem 224 32) aw' out σ' k' C') ∨
    (ExecStmt fork config {contract := contract, locals := locals} evm vaultInitializeDecimalsStmt .reverted ∧
      RDrev fork vaultBytecode g s0) := by
  have hreceiver : evalExpr? config {contract := contract, locals := locals} evm (.var "_borrowed_token_") =
      .ok (.address (AccountAddress.ofNat target.toNat)) := by
    simp only [evalExpr?, htarget, EvalResult.ofOption]
  have hbridge := staticWordCallBridgeExact (cfg := config) (pc := UInt256.ofNat 247) (next := UInt256.ofNat 283)
    (inOffset := UInt256.ofNat 252) (outOffset := UInt256.ofNat 224)
    (nextStack := fun _ => ⟨32⟩ :: target :: R)
    hs (by simp only [List.length_cons]; omega) (by native_decide) hcd hbuffer
    (fun {mem' aw' out σ' k' C'} h32 hwide rdCall => by
      have rd259 := vaultBlocks.vault_block_248_taken (by simp only [List.length_cons]; omega)
        (by decide +kernel) (by native_decide) rdCall
      have rd283 := vaultBlocks.vault_block_259_fallthrough
        (by simp only [vaultBlocks.vault_block_248_taken_stack, List.length_cons]; omega)
        (rdsCheck_ok 224 256 out.size rfl (by decide +kernel) h32 hwide) rd259
      dsimp only [vaultBlocks.vault_block_259_fallthrough_stack, vaultBlocks.vault_block_248_taken_stack] at rd283
      rw [vyperMin32 out.size hwide, Nat.min_eq_right h32] at rd283
      exact ⟨_, _, rd283⟩)
    (fun {mem' aw' out σ' k' C'} rdCall => by
      have rd252 := vaultBlocks.vault_block_248_fallthrough (by simp only [List.length_cons]; omega) rfl rdCall
      exact vaultBlocks.vault_block_252 (by simp only [vaultBlocks.vault_block_248_fallthrough_stack, List.length_cons]; omega) rd252)
    (fun {mem' aw' out σ' k' C'} hshort rdCall => by
      have rd259 := vaultBlocks.vault_block_248_taken (by simp only [List.length_cons]; omega)
        (by decide +kernel) (by native_decide) rdCall
      have rdFail := vaultBlocks.vault_block_259_taken
        (by simp only [vaultBlocks.vault_block_248_taken_stack, List.length_cons]; omega)
        (rdsCheck_short 224 256 out.size rfl (by decide +kernel) hshort) (by native_decide) rd259
      exact vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_259_taken_stack, vaultBlocks.vault_block_248_taken_stack, List.length_cons]; omega) rdFail) h
  rcases hbridge with ⟨evm', σ', out, aw', k', C', haw', h32, hwide, hcall, hs', rd283⟩ |
    ⟨evm', out, hcall, hrev⟩ | ⟨evm', out, hcall, hshort, hrev⟩
  · change RD fork vaultBytecode I g s0 (UInt256.ofNat 283) (⟨32⟩ :: target :: R)
      ((retWord out).toByteArray.write 0 mem 224 32) aw' out σ' k' C' at rd283
    have hawBound : aw'.toNat ≤ 10 := by
      rw [haw']
      exact staticCallActive_le (inOff := ⟨252⟩) (inLen := ⟨4⟩) (outOff := ⟨224⟩) (outLen := ⟨32⟩)
        haw (by decide +kernel) (by decide +kernel)
    have hword : memLoad (UInt256.ofNat 224) ((retWord out).toByteArray.write 0 mem 224 32) = retWord out :=
      memLoad_write_back _ _ 224 (by decide +kernel) (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 224 (by omega)))
    by_cases hcanon : (retWord out).toNat < 256
    · have rd294 := vaultBlocks.vault_block_283_fallthrough (by simp only [List.length_cons]; omega)
        (by rw [hword]; exact (u256_shiftRight_zero_iff _ 8 (by omega)).mpr hcanon) rd283
      dsimp only [vaultBlocks.vault_block_283_fallthrough_stack] at rd294
      rw [hword] at rd294
      refine Or.inl ⟨evm', σ', out, _, _, _, hcanon, memoryActive_le hawBound (by decide +kernel), ?_, hs', rd294⟩
      apply ExecStmt.externalCallSuccess (hperm := Or.inl rfl) (sendVal := 0) (argVals := [])
        (value := [.int (Int.ofNat (retWord out).toNat)]) hreceiver
        (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
        (by simpa only [accountAddress_ofUInt256_eq_ofNat_toNat, address_of_val] using hcall)
      change (ABI.decodeReturnValueWithMode? .vyper (.elem (.int (.uint ⟨8, by decide⟩))) out).map (fun v => [v]) = _
      rw [decodeReturn_vyper_uint_eq _ out (by decide +kernel) h32, if_pos (show (retWord out).toNat < 2 ^ (8 : Nat) from hcanon)]; rfl
    · have rdFail := vaultBlocks.vault_block_283_taken (by simp only [List.length_cons]; omega)
        (by rw [hword]; exact fun hz => hcanon ((u256_shiftRight_zero_iff _ 8 (by omega)).mp hz)) (by native_decide) rd283
      have hrev := vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_283_taken_stack, List.length_cons]; omega) rdFail
      refine Or.inr ⟨ExecStmt.externalCallReturnDecodeRevert (hperm := Or.inl rfl) (sendVal := 0) (argVals := []) hreceiver
        (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
        (by simpa only [accountAddress_ofUInt256_eq_ofNat_toNat, address_of_val] using hcall) ?_, hrev⟩
      change (ABI.decodeReturnValueWithMode? .vyper (.elem (.int (.uint ⟨8, by decide⟩))) out).map (fun v => [v]) = _
      rw [decodeReturn_vyper_uint_eq _ out (by decide +kernel) h32, if_neg (show ¬ (retWord out).toNat < 2 ^ (8 : Nat) from hcanon)]; rfl
  · exact Or.inr ⟨ExecStmt.externalCallFailure (hperm := Or.inl rfl) (sendVal := 0) (argVals := []) hreceiver
      (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
      (by simpa only [accountAddress_ofUInt256_eq_ofNat_toNat, address_of_val] using hcall), hrev⟩
  · refine Or.inr ⟨ExecStmt.externalCallReturnDecodeRevert (hperm := Or.inl rfl) (sendVal := 0) (argVals := []) hreceiver
      (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
      (by simpa only [accountAddress_ofUInt256_eq_ofNat_toNat, address_of_val] using hcall) ?_, hrev⟩
    change (ABI.decodeReturnValueWithMode? .vyper (.elem (.int (.uint ⟨8, by decide⟩))) out).map (fun v => [v]) = _
    rw [decodeReturn_vyper_uint_short _ out hshort]; rfl

end Benchmarks.CurveVault

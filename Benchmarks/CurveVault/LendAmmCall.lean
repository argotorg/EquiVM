import Benchmarks.CurveVault.StaticWordCalls
import Benchmarks.CurveVault.AmmStorage
import Benchmarks.CurveVault.RuntimeBlocks_005
import Benchmarks.CurveVault.RuntimeBlocks_006
import Benchmarks.CurveVault.RuntimeBlocks_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

abbrev vaultLendRateStmt : Stmt :=
  .externalCall (.storage {base := "_amm", steps := []}) "rate" (.intLit 0) [] "__c1" (perm := false)

theorem vaultLendRateCall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hbase : locals.get? "_amm" = none)
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 1194) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      ExecStmt fork config {contract := contract, locals := locals} evm vaultLendRateStmt
        (.ok {contract := contract, locals := locals.insert "__c1" (.int (Int.ofNat (retWord out).toNat))} evm') ∧
      SourceState s0 I σ' evm' ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat 1240) (codeOwnerStorageWord I σ ⟨2⟩ :: R)
        ((retWord out).toByteArray.write 0 (vaultBlocks.vault_block_1194_memory (mem := mem)) 320 32)
        aw' out σ' k' C') ∨
    (ExecStmt fork config {contract := contract, locals := locals} evm vaultLendRateStmt .reverted ∧ RDrev fork vaultBytecode g s0) := by
  obtain ⟨gasArg, k', C', rd⟩ := vaultBlocks.vault_block_1194 hstack h
  have hcd : config.externalABI.encode? "rate" [] = some
      ((vaultBlocks.vault_block_1194_memory (mem := mem)).readWithPadding 348 4) := by
    change ABI.encodeCallWithSelector? (selectorBytes 0x2c 0x4e 0x72 0x2e) [] [] = _
    exact vyperNullaryCallData _ _ mem 320 (by decide +kernel)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 320 (by norm_num)))
  have hbuffer : 352 ≤ (vaultBlocks.vault_block_1194_memory (mem := mem)).size :=
    toByteArray_write_size_ge_off_add32 _ _ 320 (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 320 (by norm_num)))
  have hreceiver := vaultAmmEval evm locals hbase
  rw [hs.storageRead] at hreceiver
  have hbridge := staticWordCallBridge (cfg := config) (pc := UInt256.ofNat 1219) (next := UInt256.ofNat 1240)
    (nextStack := fun _ => codeOwnerStorageWord I σ ⟨2⟩ :: R)
    (mem := vaultBlocks.vault_block_1194_memory (mem := mem)) (inOffset := UInt256.ofNat 348) (outOffset := UInt256.ofNat 320)
    hs (by simp only [List.length_cons]; omega) (by native_decide) hcd hbuffer
    (fun {mem' aw' out σ' k'' C''} h32 hwide rdCall => by
      have rdSize := vaultBlocks.vault_block_1220_taken
        (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) rdCall
      have rdNext := vaultBlocks.vault_block_1231_fallthrough
        (by simp only [vaultBlocks.vault_block_1220_taken_stack, List.length_cons]; omega)
        (ult_zero (by rw [ulit_toNat' _ hwide]; exact h32)) rdSize
      exact ⟨_, _, rdNext⟩)
    (fun {mem' aw' out σ' k'' C''} rdCall => by
      have rdFail := vaultBlocks.vault_block_1220_fallthrough
        (by simp only [List.length_cons]; omega) rfl rdCall
      exact vaultBlocks.vault_block_1224
        (by simp only [vaultBlocks.vault_block_1220_fallthrough_stack, List.length_cons]; omega) rdFail)
    (fun {mem' aw' out σ' k'' C''} hshort rdCall => by
      have rdSize := vaultBlocks.vault_block_1220_taken
        (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) rdCall
      have rdFail := vaultBlocks.vault_block_1231_taken
        (by simp only [vaultBlocks.vault_block_1220_taken_stack, List.length_cons]; omega)
        (by rw [ult_one (by rw [ulit_toNat' _ (lt_trans hshort (by decide +kernel))]; exact hshort)]; decide +kernel)
        (by native_decide) rdSize
      exact vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_1220_taken_stack, List.length_cons]; omega) rdFail) rd
  rcases hbridge with ⟨evm', σ', out, aw', k'', C'', h32, _, hcall, hs', rdNext⟩ |
    ⟨evm', out, hcall, hrev⟩ | ⟨evm', out, hcall, hshort, hrev⟩
  · refine Or.inl ⟨evm', σ', out, aw', k'', C'', ?_, hs', rdNext⟩
    apply ExecStmt.externalCallSuccess (hperm := Or.inl rfl) (sendVal := 0) (argVals := [])
      (value := [.int (Int.ofNat (retWord out).toNat)]) hreceiver
      (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
      (by simpa only [address_of_val] using hcall)
    change (ABI.decodeReturnValueWithMode? .vyper (.elem (.int (.uint ⟨256, by decide⟩))) out).map (fun v => [v]) = _
    rw [decodeReturn_vyper_uint256_ok out h32]; rfl
  · exact Or.inr ⟨ExecStmt.externalCallFailure (hperm := Or.inl rfl) (sendVal := 0) (argVals := []) hreceiver
      (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
      (by simpa only [address_of_val] using hcall), hrev⟩
  · refine Or.inr ⟨ExecStmt.externalCallReturnDecodeRevert (hperm := Or.inl rfl) (sendVal := 0) (argVals := []) hreceiver
      (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
      (by simpa only [address_of_val] using hcall) ?_, hrev⟩
    change (ABI.decodeReturnValueWithMode? .vyper (.elem (.int (.uint ⟨256, by decide⟩))) out).map (fun v => [v]) = _
    rw [decodeReturn_vyper_uint256_short out hshort]; rfl
end Benchmarks.CurveVault

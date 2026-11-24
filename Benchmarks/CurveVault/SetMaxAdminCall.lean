import Benchmarks.CurveVault.FactoryStorage
import Benchmarks.CurveVault.MutatingLock
import Benchmarks.CurveVault.StaticWordCalls
import Benchmarks.CurveVault.RuntimeBlocks_004
import Benchmarks.CurveVault.RuntimeBlocks_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

abbrev vaultSetMaxFunction : FunctionDecl := contract.functions[0]!
abbrev vaultSetMaxAdminStmt : Stmt := vaultSetMaxFunction.body[0]!

theorem vaultSetMaxAdminCall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hbase : locals.get? "_factory" = none)
    (hfactory : (codeOwnerStorageWord I σ ⟨4⟩).toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 861) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      (retWord out).toNat < EVM.addressModulus ∧ (codeOwnerStorageWord I σ' ⟨4⟩).toNat < EVM.addressModulus ∧
      ExecStmt fork config {contract := contract, locals := locals} (vaultSetLock evm ⟨1⟩) vaultSetMaxAdminStmt
        (.ok {contract := contract, locals := locals.insert "factory_admin" (.address (AccountAddress.ofNat (retWord out).toNat))} evm') ∧
      SourceState s0 I σ' evm' ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat 932) (retWord out :: ⟨32⟩ :: codeOwnerStorageWord I σ ⟨4⟩ :: R)
        ((retWord out).toByteArray.write 0 (vaultBlocks.vault_block_861_memory (mem := mem)) 64 32)
        aw' out σ' k' C') ∨
    (ExecStmt fork config {contract := contract, locals := locals} (vaultSetLock evm ⟨1⟩) vaultSetMaxAdminStmt .reverted ∧
      RDrev fork vaultBytecode g s0) := by
  let evm0 := vaultSetLock evm ⟨1⟩
  let σ0 := tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨1⟩
  have hs0 : SourceState s0 I σ0 evm0 := by
    unfold evm0 vaultSetLock
    rw [hs.env]
    exact sourceStateTransientWrite hs ⟨0⟩ ⟨1⟩
  have hreceiver := vaultFactoryEval evm0 locals hbase
  rw [hs0.storageRead] at hreceiver
  change evalExpr? config {contract := contract, locals := locals} evm0
    (.storage {base := "_factory", steps := []}) =
      .ok (.address (AccountAddress.ofUInt256 (codeOwnerStorageWord I σ0 ⟨4⟩))) at hreceiver
  dsimp only [σ0] at hreceiver
  rw [codeOwnerStorageWord_tstore] at hreceiver
  obtain ⟨gasArg, k0, C0, rd886⟩ := vaultBlocks.vault_block_861 hstack hperm h
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 886)
    (gasArg :: codeOwnerStorageWord I σ0 ⟨4⟩ :: UInt256.ofNat 92 :: ⟨4⟩ :: ⟨64⟩ :: ⟨32⟩ ::
      codeOwnerStorageWord I σ0 ⟨4⟩ :: R) _ _ rdata σ0 k0 C0 at rd886
  dsimp only [σ0] at rd886
  rw [codeOwnerStorageWord_tstore] at rd886
  have hbuffer : 96 ≤ (vaultBlocks.vault_block_861_memory (mem := mem)).size :=
    toByteArray_write_size_ge_off_add32 _ _ 64 (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 64 (by omega)))
  have hbridge := staticWordCallBridge (cfg := config) (pc := UInt256.ofNat 886) (next := UInt256.ofNat 921)
    (mem := vaultBlocks.vault_block_861_memory (mem := mem))
    (inOffset := UInt256.ofNat 92) (outOffset := UInt256.ofNat 64)
    (nextStack := fun _ => ⟨32⟩ :: codeOwnerStorageWord I σ ⟨4⟩ :: R)
    hs0 (by simp only [List.length_cons]; omega) (by native_decide) (vaultAdminCalldata mem) hbuffer
    (fun {mem' aw' out σ' k' C'} h32 hwide rdCall => by
      have rd898 := vaultBlocks.vault_block_887_taken (by simp only [List.length_cons]; omega)
        (by decide +kernel) (by native_decide) rdCall
      have rd921 := vaultBlocks.vault_block_898_fallthrough
        (by simp only [vaultBlocks.vault_block_887_taken_stack, List.length_cons]; omega)
        (rdsCheck_ok 64 96 out.size rfl (by decide +kernel) h32 hwide) rd898
      dsimp only [vaultBlocks.vault_block_898_fallthrough_stack, vaultBlocks.vault_block_887_taken_stack] at rd921
      rw [vyperMin32 out.size hwide, Nat.min_eq_right h32] at rd921
      exact ⟨_, _, rd921⟩)
    (fun {mem' aw' out σ' k' C'} rdCall => by
      have rd891 := vaultBlocks.vault_block_887_fallthrough (by simp only [List.length_cons]; omega) rfl rdCall
      exact vaultBlocks.vault_block_891 (by simp only [vaultBlocks.vault_block_887_fallthrough_stack, List.length_cons]; omega) rd891)
    (fun {mem' aw' out σ' k' C'} hshort rdCall => by
      have rd898 := vaultBlocks.vault_block_887_taken (by simp only [List.length_cons]; omega)
        (by decide +kernel) (by native_decide) rdCall
      have rdFail := vaultBlocks.vault_block_898_taken
        (by simp only [vaultBlocks.vault_block_887_taken_stack, List.length_cons]; omega)
        (rdsCheck_short 64 96 out.size rfl (by decide +kernel) hshort) (by native_decide) rd898
      exact vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_898_taken_stack, vaultBlocks.vault_block_887_taken_stack, List.length_cons]; omega) rdFail) rd886
  rcases hbridge with ⟨evm', σ', out, aw', k', C', h32, hwide, hcall, hs', rd921⟩ |
    ⟨evm', out, hcall, hrev⟩ | ⟨evm', out, hcall, hshort, hrev⟩
  · change RD fork vaultBytecode I g s0 (UInt256.ofNat 921)
      (⟨32⟩ :: codeOwnerStorageWord I σ ⟨4⟩ :: R)
      ((retWord out).toByteArray.write 0 (vaultBlocks.vault_block_861_memory (mem := mem)) 64 32)
      aw' out σ' k' C' at rd921
    have hword : memLoad (UInt256.ofNat 64)
        ((retWord out).toByteArray.write 0 (vaultBlocks.vault_block_861_memory (mem := mem)) 64 32) = retWord out :=
      memLoad_write_back _ _ 64 (by decide +kernel) (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 64 (by omega)))
    by_cases hcanon : (retWord out).toNat < EVM.addressModulus
    · have rd932 := vaultBlocks.vault_block_921_fallthrough (by simp only [List.length_cons]; omega)
        (by rw [hword]; exact u256_shiftRight160_zero_of_lt _ hcanon) rd921
      dsimp only [vaultBlocks.vault_block_921_fallthrough_stack] at rd932
      rw [hword] at rd932
      refine Or.inl ⟨evm', σ', out, _, _, _, hcanon, ?_, ?_, hs', rd932⟩
      · rw [sourceStateStaticStorageRead hs0 hs' hcall ⟨4⟩]
        dsimp only [σ0]
        rw [codeOwnerStorageWord_tstore]
        exact hfactory
      · apply ExecStmt.externalCallSuccess (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (sendVal := 0) (argVals := [])
          (value := [.address (AccountAddress.ofNat (retWord out).toNat)]) hreceiver
          (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
          (by simpa only [address_of_val] using hcall)
        change (ABI.decodeReturnValueWithMode? .vyper (.elem .address) out).map (fun v => [v]) = _
        rw [decodeReturn_vyper_address_ok out h32 hcanon]; rfl
    · have rdFail := vaultBlocks.vault_block_921_taken (by simp only [List.length_cons]; omega)
        (by rw [hword]; exact fun hz => hcanon (u256_lt_addressModulus_of_shiftRight160_zero _ hz)) (by native_decide) rd921
      have hrev := vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_921_taken_stack, List.length_cons]; omega) rdFail
      refine Or.inr ⟨ExecStmt.externalCallReturnDecodeRevert (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (sendVal := 0) (argVals := []) hreceiver
        (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
        (by simpa only [address_of_val] using hcall) ?_, hrev⟩
      change (ABI.decodeReturnValueWithMode? .vyper (.elem .address) out).map (fun v => [v]) = _
      rw [decodeReturn_vyper_address_noncanon out h32 hcanon]; rfl
  · exact Or.inr ⟨ExecStmt.externalCallFailure (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (sendVal := 0) (argVals := []) hreceiver
      (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
      (by simpa only [address_of_val] using hcall), hrev⟩
  · refine Or.inr ⟨ExecStmt.externalCallReturnDecodeRevert (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (sendVal := 0) (argVals := []) hreceiver
      (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
      (by simpa only [address_of_val] using hcall) ?_, hrev⟩
    change (ABI.decodeReturnValueWithMode? .vyper (.elem .address) out).map (fun v => [v]) = _
    rw [decodeReturn_vyper_address_short out hshort]; rfl

end Benchmarks.CurveVault

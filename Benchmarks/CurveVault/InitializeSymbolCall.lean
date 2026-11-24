import Benchmarks.CurveVault.InitializeSymbolDecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

abbrev vaultInitializeSymbolStmt : Stmt := initializeTransition.body[10]!

theorem vaultInitializeSymbolCall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {locals : Store} {gasArg target : UInt256}
    (hs : SourceState s0 I σ evm)
    (htarget : locals.get? "_borrowed_token_" = some (.address (AccountAddress.ofNat target.toNat)))
    (hcd : config.externalABI.encode? "symbol" [] = some (mem.readWithPadding 316 4))
    (hmem : mem.size = 320) (haw : aw.toNat ≤ 10) (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 388)
      (gasArg :: target :: ⟨316⟩ :: ⟨4⟩ :: ⟨288⟩ :: ⟨96⟩ :: target :: R) mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (size ptr : UInt256) (mem' out : ByteArray)
        (aw' : UInt256) (k' C' : Nat),
      ExecStmt fork config {contract := contract, locals := locals} evm vaultInitializeSymbolStmt
        (.ok {contract := contract, locals := (locals.insert "borrowed_symbol"
          (vaultBorrowedSymbol size.toNat (mem'.readWithPadding (ptr.toNat + 32) 32)))} evm') ∧
      SourceState s0 I σ' evm' ∧ size.toNat ≤ 32 ∧ ptr.toNat ≤ 352 ∧
      ptr.toNat + 32 ≤ mem'.size ∧ mem'.size ≤ 384 ∧
      memLoad ptr mem' = size ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat 476)
        (size :: ptr :: UInt256.ofNat (min out.size 96) :: target :: R) mem' aw' out σ' k' C') ∨
    (ExecStmt fork config {contract := contract, locals := locals} evm vaultInitializeSymbolStmt .reverted ∧
      RDrev fork vaultBytecode g s0) := by
  have hreceiver : evalExpr? config {contract := contract, locals := locals} evm (.var "_borrowed_token_") =
      .ok (.address (AccountAddress.ofNat target.toNat)) := by
    simp only [evalExpr?, htarget, EvalResult.ofOption]
  obtain ⟨evm', σ', z, out, k', C', hcall, hs', rd389, hout⟩ :=
    typedStaticCallBridge h hs (by native_decide) hcd (by decide +kernel)
      (by simp only [List.length_cons]; omega)
  have hwide : out.size < UInt256.size := lt_trans hout (by decide +kernel)
  cases z with
  | false =>
    have rd393 := vaultBlocks.vault_block_389_fallthrough
      (by simp only [List.length_cons]; omega) rfl rd389
    exact Or.inr ⟨ExecStmt.externalCallFailure (hperm := Or.inl rfl) (sendVal := 0) (argVals := []) hreceiver
      (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
      (by simpa only [accountAddress_ofUInt256_eq_ofNat_toNat, address_of_val] using hcall),
      vaultBlocks.vault_block_393 (by simp only [vaultBlocks.vault_block_389_fallthrough_stack, List.length_cons]; omega) rd393⟩
  | true =>
    have rd400 := vaultBlocks.vault_block_389_taken
      (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) rd389
    have hmin := vyperMin out.size 96 hwide (by decide +kernel)
    have hlen : (UInt256.ofNat 288 + UInt256.ofNat (min out.size 96)).toNat = 288 + min out.size 96 :=
      uadd_ofNat_toNat (by decide +kernel) (by change min out.size 96 < 2 ^ 256; omega)
        (by change 288 + min out.size 96 < 2 ^ 256; omega)
    by_cases h32 : 32 ≤ out.size
    swap
    · have rdFail := vaultBlocks.vault_block_400_taken
        (by simp only [vaultBlocks.vault_block_389_taken_stack, List.length_cons]; omega)
        (by rw [hmin]; rw [ugt_one (by rw [hlen]; change _ < 320; omega)]; decide +kernel)
        (by native_decide) rd400
      refine Or.inr ⟨ExecStmt.externalCallReturnDecodeRevert (hperm := Or.inl rfl) (sendVal := 0) (argVals := []) hreceiver
        (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
        (by simpa only [accountAddress_ofUInt256_eq_ofNat_toNat, address_of_val] using hcall) ?_,
        vaultBlocks.vault_block_8284
          (by simp only [vaultBlocks.vault_block_400_taken_stack, vaultBlocks.vault_block_389_taken_stack, List.length_cons]; omega) rdFail⟩
      exact decodeTokenSymbol_short out (by omega)
    have rd425 := vaultBlocks.vault_block_400_fallthrough
      (by simp only [vaultBlocks.vault_block_389_taken_stack, List.length_cons]; omega)
      (by rw [hmin]; exact ugt_zero (by rw [hlen]; change 320 ≤ _; omega)) rd400
    dsimp only [vaultBlocks.vault_block_400_fallthrough_stack, vaultBlocks.vault_block_389_taken_stack] at rd425
    rw [hmin] at rd425
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 425)
      (UInt256.ofNat (min out.size 96) :: target :: R)
      (out.write 0 mem 288 (min (UInt256.ofNat 96) (UInt256.ofNat out.size)).toNat) _ out σ' _ _ at rd425
    rw [vaultSymbolCallMemory_eq mem out hmem h32 hwide] at rd425
    have haw' : (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat 316 4) 288 96)).toNat ≤ 12 :=
      staticCallActive_le (inOff := ⟨316⟩) (inLen := ⟨4⟩) (outOff := ⟨288⟩) (outLen := ⟨96⟩)
        (by omega) (by decide +kernel) (by decide +kernel)
    rcases vaultInitializeSymbolDecode hmem h32 haw' hstack rd425 with
      ⟨size, ptr, aw'', k'', C'', hn, hp, hfull, hdecode, hm, rd476⟩ | ⟨hdecode, hrev⟩
    · refine Or.inl ⟨evm', σ', size, ptr, _, out, aw'', k'', C'', ?_, hs', hn, hp, hfull, ?_, hm, rd476⟩
      · apply ExecStmt.externalCallSuccess (hperm := Or.inl rfl) (sendVal := 0) (argVals := [])
          (value := [vaultBorrowedSymbol size.toNat
            ((vaultSymbolCallMemory mem out).readWithPadding (ptr.toNat + 32) 32)]) hreceiver
          (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
          (by simpa only [accountAddress_ofUInt256_eq_ofNat_toNat, address_of_val] using hcall)
        exact hdecode
      · rw [vaultSymbolCallMemory_size mem out hmem]
        omega
    · exact Or.inr ⟨ExecStmt.externalCallReturnDecodeRevert (hperm := Or.inl rfl) (sendVal := 0) (argVals := []) hreceiver
        (by simp [evalExpr?, pure]) (by simp [evalExprs?, pure])
        (by simpa only [accountAddress_ofUInt256_eq_ofNat_toNat, address_of_val] using hcall) hdecode, hrev⟩

end Benchmarks.CurveVault

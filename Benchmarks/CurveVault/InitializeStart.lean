import Benchmarks.CurveVault.InitializeDecimalsCall
import Benchmarks.CurveVault.InitializeStorage
import Benchmarks.CurveVault.Memory

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

theorem vaultInitializeBorrowedDecimals {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {locals : Store} {token : UInt256}
    (hs : SourceState s0 I σ evm)
    (ht : locals.get? "_borrowed_token_" = some (.address (AccountAddress.ofNat token.toNat)))
    (hbase : locals.get? "_borrowed_token" = none)
    (hmt : memLoad (UInt256.ofNat 128) mem = token) (hcanon : token.toNat < EVM.addressModulus)
    (hperm : I.perm = true) (haw : aw.toNat ≤ 10) (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 221) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (decimals : UInt256) (mem' out : ByteArray)
        (aw' : UInt256) (k' C' : Nat),
      decimals.toNat < 256 ∧ aw'.toNat ≤ 10 ∧
      ExecBlock fork config {contract := contract, locals := locals} evm (initializeTransition.body.drop 2 |>.take 2)
        (.ok {contract := contract, locals := locals.insert "__c0" (.int (Int.ofNat decimals.toNat))} evm') ∧
      SourceState s0 I σ' evm' ∧ 256 ≤ mem'.size ∧ mem'.size = max mem.size 256 ∧
      WordMemoryRange mem mem' 0 224 ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat 294) (decimals :: ⟨32⟩ :: token :: R) mem' aw' out σ' k' C') ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm (initializeTransition.body.drop 2 |>.take 2)
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  let evm0 := Stele.EVM.storageStore evm I.codeOwner ⟨0⟩ token
  let σ0 := sstoreAccountMap I.codeOwner σ ⟨0⟩ token
  let mem0 := vaultBlocks.vault_block_221_memory (mem := mem)
  have hs0 : SourceState s0 I σ0 evm0 := hs.storageWrite ⟨0⟩ token
  have hword : UInt256.ofNat (AccountAddress.ofNat token.toNat).val = token := by
    simpa only [keyValueToWord_address] using keyValueToWord_address_of_canonical token hcanon
  have hassign : ExecStmt fork config {contract := contract, locals := locals} evm initializeTransition.body[2]!
      (.ok {contract := contract, locals := locals} evm0) :=
    ExecStmt.assign (hperm := Or.inr (by simpa only [hs.env] using hperm)) (by simp only [evalExpr?, ht, EvalResult.ofOption]; rfl)
      (by simpa only [hs.env, hword] using
        vaultAssignScalarAddress evm locals "_borrowed_token" ⟨0⟩ (AccountAddress.ofNat token.toNat) hbase rfl rfl)
  obtain ⟨gasArg, k0, C0, rd247⟩ := vaultBlocks.vault_block_221 hstack hperm h
  dsimp only [vaultBlocks.vault_block_221_stack] at rd247
  rw [hmt] at rd247
  have hgap (m : ByteArray) : 224 - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 224 (by omega))
  have hbuffer : 256 ≤ mem0.size := toByteArray_write_size_ge_off_add32 _ _ 224 (hgap mem)
  have hcd : config.externalABI.encode? "decimals" [] = some (mem0.readWithPadding 252 4) :=
    vyperNullaryCallData _ _ mem 224 (by decide +kernel) (hgap mem)
  rcases vaultInitializeDecimalsCall hs0 ht hcd hbuffer
    (memoryActive_le (memoryActive_le (memoryActive_le haw (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) hstack rd247 with
    ⟨evm', σ', out, aw', k', C', hdec, haw', hcall, hs', rd294⟩ | ⟨hcall, hrev⟩
  · refine Or.inl ⟨evm', σ', retWord out, _, out, aw', k', C', hdec, haw',
      ExecBlock.consNormal hassign (ExecBlock.consNormal hcall ExecBlock.nil), hs',
      toByteArray_write_size_ge_off_add32 _ _ 224 (hgap mem0), ?_, ?_, rd294⟩
    · change (writeWord mem0 224 (retWord out)).size = max mem.size 256
      rw [writeWord_size _ _ _ (hgap mem0)]
      change max (writeWord mem 224 (UInt256.ofNat 826074471)).size 256 = max mem.size 256
      rw [writeWord_size _ _ _ (hgap mem)]
      omega
    ·
      exact (wordMemoryRange_write mem (UInt256.ofNat 826074471) 224 0 224 (hgap mem) (Or.inl (by omega))).trans
        (wordMemoryRange_write mem0 (retWord out) 224 0 224 (hgap mem0) (Or.inl (by omega)))
  · exact Or.inr ⟨ExecBlock.consNormal hassign (ExecBlock.consRevert hcall), hrev⟩

end Benchmarks.CurveVault

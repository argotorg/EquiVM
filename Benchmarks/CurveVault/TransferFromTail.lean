import Benchmarks.CurveVault.TransferInternal
import Benchmarks.CurveVault.MutatingLock
import Benchmarks.CurveVault.RuntimeBlocks_020

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

abbrev vaultTransferFromFunction : FunctionDecl := contract.functions[20]!

theorem vaultTransferFromTail {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {sender recipient : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 256 ≤ mem.size)
    (hmf : memLoad (UInt256.ofNat 192) mem = sender)
    (hmt : memLoad (UInt256.ofNat 224) mem = recipient)
    (hcanon0 : sender.toNat < EVM.addressModulus) (hcanon1 : recipient.toNat < EVM.addressModulus)
    (hf : locals.get? "_from" = some (.address (AccountAddress.ofNat sender.toNat)))
    (ht : locals.get? "_to" = some (.address (AccountAddress.ofNat recipient.toNat)))
    (hv : locals.get? "_value" = some (.int (Int.ofNat (calldataWord I.calldata 68).toNat)))
    (hperm : I.perm = true) (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 5845) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap),
      ExecBlock fork config {contract := contract, locals := locals} evm (vaultTransferFromFunction.body.drop 2)
        (.returned {contract := contract, locals := locals.insert "__c1" .unit} evm' (some [.bool true])) ∧
      SourceState s0 I σ' evm' ∧
      RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) (⟨1⟩ : UInt256).toByteArray) ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm (vaultTransferFromFunction.body.drop 2)
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  let value := calldataWord I.calldata 68
  let copied := mem.write 192 mem 64 64
  let argsMem := value.toByteArray.write 0 copied 128 32
  have hgap : 128 - copied.size < USize.size := lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 128 (by omega))
  have hcopied : copied.size = mem.size := by
    rw [copyWindow_size mem mem 192 64 64 (by omega) hsize (by omega)]
    omega
  have hargsSize : 160 ≤ argsMem.size := toByteArray_write_size_ge_off_add32 _ _ 128 hgap
  have hfArgs : memLoad (UInt256.ofNat 64) argsMem = sender := by
    rw [memLoad_below_write _ _ 128 64 (by rw [hcopied]; omega) (by omega) hgap (by decide +kernel)]
    rw [show memLoad (UInt256.ofNat 64) copied = memLoad (UInt256.ofNat 192) mem from
      memLoad_copyWindow mem mem 192 64 64 0 (by omega) hsize (by omega) (by omega) (by decide +kernel) (by decide +kernel), hmf]
  have htArgs : memLoad (UInt256.ofNat 96) argsMem = recipient := by
    rw [memLoad_below_write _ _ 128 96 (by rw [hcopied]; omega) (by omega) hgap (by decide +kernel)]
    rw [show memLoad (UInt256.ofNat 96) copied = memLoad (UInt256.ofNat 224) mem from
      memLoad_copyWindow mem mem 192 64 64 32 (by omega) hsize (by omega) (by omega) (by decide +kernel) (by decide +kernel), hmt]
  have hvArgs : memLoad (UInt256.ofNat 128) argsMem = value := memLoad_write_back _ _ 128 (by decide +kernel) hgap
  have rd8133 := vaultBlocks.vault_block_5845 (by omega) (by native_decide) h
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 8133) (UInt256.ofNat 5866 :: R) argsMem _ rdata σ _ _ at rd8133
  have hargs : evalExprs? config {contract := contract, locals := locals} evm
      [.var "_from", .var "_to", .var "_value"] =
      .ok [.address (AccountAddress.ofNat sender.toNat), .address (AccountAddress.ofNat recipient.toNat),
        .int (Int.ofNat value.toNat)] := by
    simp only [evalExprs?, evalExpr?, hf, ht, hv, EvalResult.ofOption, EvalResult.bind, bind, pure]
    rfl
  rcases vaultTransferRoutine hs hargsSize hfArgs htArgs hvArgs hcanon0 hcanon1 hperm hstack (by native_decide) rd8133 with
    ⟨evm', σ', aw', k', C', hcallee, hs', rd5866⟩ | ⟨hcallee, hrev⟩
  swap
  · exact Or.inr ⟨ExecBlock.consRevert (internalCallFunctionRevert
      (callee := vaultTransferFunction) hargs rfl rfl hcallee), hrev⟩
  have hcall := internalCallFunctionReturn (caller := {contract := contract, locals := locals})
    (callee := vaultTransferFunction) (name := "_transfer") (retVar := "__c1") hargs rfl rfl hcallee
  have hret := vaultBlocks.vault_block_5866 (by omega) hperm rd5866
  change RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩)
    (((⟨1⟩ : UInt256).toByteArray.write 0 _ 288 32).readWithPadding 288 32) at hret
  rw [toByteArray_write_read_back_of_gap _ _ _
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 288 (by omega)))] at hret
  exact Or.inl ⟨evm', σ', ExecBlock.consNormal hcall
    (ExecBlock.consReturn (ExecStmt.return (by simp [evalExprs?, evalExpr?, EvalResult.bind, pure, bind]))), hs', hret⟩

end Benchmarks.CurveVault

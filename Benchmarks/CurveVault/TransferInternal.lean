import Benchmarks.CurveVault.TransferTail

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultTransferRoutine {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {sender recipient value returnPc : UInt256} {R : List UInt256}
    (hs : SourceState s0 I σ evm) (hsize : 160 ≤ mem.size)
    (hmf : memLoad (UInt256.ofNat 64) mem = sender)
    (hmt : memLoad (UInt256.ofNat 96) mem = recipient)
    (hmv : memLoad (UInt256.ofNat 128) mem = value)
    (hcanon0 : sender.toNat < EVM.addressModulus) (hcanon1 : recipient.toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J vaultBytecode 0).contains returnPc = true)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 8133) (returnPc :: R) mem aw rdata σ k C) :
    let locals := vaultTransferLocals (AccountAddress.ofNat sender.toNat) (AccountAddress.ofNat recipient.toNat) value
    (∃ (evm' : State) (σ' : AccountMap) (aw' : UInt256) (k' C' : Nat),
      ExecFuncBody fork config {contract := contract, locals := locals} evm vaultTransferFunction.body
        (.returned {contract := contract, locals := locals} evm' none) ∧
      SourceState s0 I σ' evm' ∧
      RD fork vaultBytecode I g s0 returnPc R (vaultTransferMemory mem sender recipient value) aw' rdata σ' k' C') ∨
    (ExecFuncBody fork config {contract := contract, locals := locals} evm vaultTransferFunction.body .reverted ∧
      RDrev fork vaultBytecode g s0) := by
  let locals := vaultTransferLocals (AccountAddress.ofNat sender.toNat) (AccountAddress.ofNat recipient.toNat) value
  have hb : locals.get? "balanceOf" = none := by simp [locals, vaultTransferLocals]
  have hf : locals.get? "_from" = some (.address (AccountAddress.ofNat sender.toNat)) := by
    simp [locals, vaultTransferLocals]
  have ht : locals.get? "_to" = some (.address (AccountAddress.ofNat recipient.toNat)) := by
    simp only [locals, vaultTransferLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  have hv : locals.get? "_value" = some (.int (Int.ofNat value.toNat)) := by
    simp only [locals, vaultTransferLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  rcases vaultTransferGuard hs ht hmt hcanon1 (by simp only [List.length_cons]; omega) h with
    ⟨hguard, aw0, k0, C0, rd8161⟩ | ⟨hguard, hrev⟩
  swap
  · exact Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.requireFalse hguard)), hrev⟩
  rcases vaultTransferTail hs hsize hmf hmt hmv hcanon0 hcanon1 hb hf ht hv hperm hstack hvalid rd8161 with
    ⟨evm', σ', aw', k', C', htail, hs', rdReturn⟩ | ⟨htail, hrev⟩
  · exact Or.inl ⟨evm', σ', aw', k', C',
      ExecFuncBody.execBlockOK (ExecBlock.consNormal (ExecStmt.requireTrue hguard) htail), hs', rdReturn⟩
  · exact Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hguard) htail), hrev⟩

end Benchmarks.CurveVault

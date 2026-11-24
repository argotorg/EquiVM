import Benchmarks.CurveVault.TokenInternal

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultTokenForward {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {token sender recipient amount returnPc : UInt256} {R : List UInt256} {locals : Store}
    {args : List Expr} {retVar : Ident}
    (hs : SourceState s0 I σ evm) (hsize : 192 ≤ mem.size)
    (hmt : memLoad (UInt256.ofNat 64) mem = token)
    (hmf : memLoad (UInt256.ofNat 96) mem = sender)
    (hmr : memLoad (UInt256.ofNat 128) mem = recipient)
    (hma : memLoad (UInt256.ofNat 160) mem = amount)
    (hargs : evalExprs? config {contract := contract, locals := locals} evm args =
      .ok [.address (AccountAddress.ofUInt256 token), .int (Int.ofNat sender.toNat),
        .int (Int.ofNat recipient.toNat), .int (Int.ofNat amount.toNat)])
    (hperm : I.perm = true) (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J vaultBytecode 0).contains returnPc = true)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 7556) (returnPc :: R) mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (mem' out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      ExecStmt fork config {contract := contract, locals := locals} evm (.internalCall "tkn_transfer_from" args retVar)
        (.ok {contract := contract, locals := locals.insert retVar .unit} evm') ∧
      SourceState s0 I σ' evm' ∧ WordMemoryRange mem mem' 352 UInt256.size ∧
      RD fork vaultBytecode I g s0 returnPc R mem' aw' out σ' k' C') ∨
    (ExecStmt fork config {contract := contract, locals := locals} evm (.internalCall "tkn_transfer_from" args retVar)
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  let calleeLocals := vaultTokenLocals (AccountAddress.ofUInt256 token) sender recipient amount
  rcases vaultTokenRoutine (locals := calleeLocals) hs hsize hmt hmf hmr hma
    (by simp [calleeLocals, vaultTokenLocals])
    (by simp only [calleeLocals, vaultTokenLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
    (by simp only [calleeLocals, vaultTokenLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
    (by simp only [calleeLocals, vaultTokenLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
    hperm hstack hvalid h with
      ⟨evm', σ', mem', out, locals', aw', k', C', hcallee, hs', hframe, rd⟩ | ⟨hcallee, hrev⟩
  · exact Or.inl ⟨evm', σ', mem', out, aw', k', C',
      internalCallFunctionReturn (callee := vaultTokenFunction) hargs rfl rfl hcallee, hs', hframe, rd⟩
  · exact Or.inr ⟨internalCallFunctionRevert (callee := vaultTokenFunction) hargs rfl rfl hcallee, hrev⟩

end Benchmarks.CurveVault

import Benchmarks.CurveVault.DebitInternal
import Benchmarks.CurveVault.MutationEntry

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultDebitEntryBody (isWithdraw : Bool) : List Stmt :=
  [.require vaultLockExpr, vaultLockAssignStmt ⟨1⟩,
    .internalCall (vaultDebitFunction isWithdraw).name
      [.var (if isWithdraw then "_assets" else "_shares"), .var "_receiver", .var "_owner"] "__r",
    vaultLockAssignStmt ⟨0⟩, .return [.var "__r"]]

theorem vaultDebitEntry (isWithdraw : Bool) {σ σ₀ A I} {g : UInt256} {t : TransitionDecl}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    {decoded locals : Store} {receiver owner : UInt256} {stmts : List Stmt}
    (hcode : I.code = vaultBytecode) (hd : dispatchMsg contract I.calldata = some t)
    (hdec : config.externalABI.decodeCalldata? (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some decoded)
    (hbody : t.body = stmts ++ vaultDebitEntryBody isWithdraw)
    (hretTy : t.returnType = [.elem (.int (.uint ⟨256, by decide⟩))])
    (hprefix : ExecBlock fork config {contract := contract, locals := decoded}
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) stmts
      (.ok {contract := contract, locals := locals} (initState σ σ₀ (Sat256.ofUInt256 g) A I)))
    (ha : locals.get? (if isWithdraw then "_assets" else "_shares") = some (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
    (hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (ho : locals.get? "_owner" = some (.address (AccountAddress.ofNat owner.toNat)))
    (hmo : memLoad (UInt256.ofNat 608) mem = owner) (hocanon : owner.toNat < EVM.addressModulus)
    (hsize : 640 ≤ mem.size) (hmr : memLoad (UInt256.ofNat 576) mem = receiver)
    (hcanon : receiver.toNat < EVM.addressModulus) (hstack : R.length + 14 ≤ 1024)
    (h : RD fork vaultBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (UInt256.ofNat (if isWithdraw then 4178 else 5080)) R mem aw rdata σ k C) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hentryPc : (vaultDebitFlow isWithdraw).lockEntry = (if isWithdraw then 4178 else 5080) := by
    cases isWithdraw <;> rfl
  have hbodyPc : (vaultDebitFlow isWithdraw).bodyEntry = (if isWithdraw then 4188 else 5090) := by
    cases isWithdraw <;> rfl
  refine vaultMutationEntry (vaultDebitFlow isWithdraw) (R := R) hcode hd hdec hbody hretTy hprefix (by omega)
    (by simpa only [hentryPc] using h) ?_
  intro aw0 k0 C0 hperm rdBody
  rw [hbodyPc] at rdBody
  have hargs : evalExprs? config {contract := contract, locals := locals}
      (vaultSetLock (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1⟩)
      [.var (if isWithdraw then "_assets" else "_shares"), .var "_receiver", .var "_owner"] =
      .ok [.int (Int.ofNat (calldataWord I.calldata 4).toNat), .address (AccountAddress.ofNat receiver.toNat),
        .address (AccountAddress.ofNat owner.toNat)] := by
    simp only [evalExprs?, evalExpr?, ha, hr, ho, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rcases vaultDebitRoutine isWithdraw SourceState.init hsize hmr hmo hcanon hocanon hperm hstack rdBody with
    ⟨evm1, σ1, locals1, value, hcallee, hs1, hret⟩ | ⟨hcallee, hrev⟩
  · exact Or.inl ⟨evm1, σ1, value, internalCallFunctionReturn (callee := vaultDebitFunction isWithdraw)
      hargs (by cases isWithdraw <;> rfl) (by cases isWithdraw <;> rfl) hcallee, hs1, hret⟩
  · exact Or.inr ⟨internalCallFunctionRevert (callee := vaultDebitFunction isWithdraw)
      hargs (by cases isWithdraw <;> rfl) (by cases isWithdraw <;> rfl) hcallee, hrev⟩

end Benchmarks.CurveVault

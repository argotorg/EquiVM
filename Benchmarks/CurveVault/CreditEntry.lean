import Benchmarks.CurveVault.CreditInternal
import Benchmarks.CurveVault.MutationEntry

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultCreditEntryBody (isDeposit : Bool) : List Stmt :=
  [.require vaultLockExpr, vaultLockAssignStmt ⟨1⟩,
    .internalCall (vaultCreditFunction isDeposit).name
      [.var (if isDeposit then "_assets" else "_shares"), .var "_receiver"] "__r",
    vaultLockAssignStmt ⟨0⟩, .return [.var "__r"]]

theorem vaultCreditEntry (isDeposit : Bool) {σ σ₀ A I} {g : UInt256} {t : TransitionDecl}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    {decoded locals : Store} {receiver : UInt256} {stmts : List Stmt}
    (hcode : I.code = vaultBytecode) (hd : dispatchMsg contract I.calldata = some t)
    (hdec : config.externalABI.decodeCalldata? (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some decoded)
    (hbody : t.body = stmts ++ vaultCreditEntryBody isDeposit)
    (hretTy : t.returnType = [.elem (.int (.uint ⟨256, by decide⟩))])
    (hprefix : ExecBlock fork config {contract := contract, locals := decoded}
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) stmts
      (.ok {contract := contract, locals := locals} (initState σ σ₀ (Sat256.ofUInt256 g) A I)))
    (ha : locals.get? (if isDeposit then "_assets" else "_shares") = some (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
    (hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (hsize : 608 ≤ mem.size) (hmr : memLoad (UInt256.ofNat 576) mem = receiver)
    (hcanon : receiver.toNat < EVM.addressModulus) (hstack : R.length + 14 ≤ 1024)
    (h : RD fork vaultBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (UInt256.ofNat (if isDeposit then 2159 else 3162)) R mem aw rdata σ k C) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hentryPc : (vaultCreditFlow isDeposit).lockEntry = (if isDeposit then 2159 else 3162) := by
    cases isDeposit <;> rfl
  have hbodyPc : (vaultCreditFlow isDeposit).bodyEntry = (if isDeposit then 2169 else 3172) := by
    cases isDeposit <;> rfl
  refine vaultMutationEntry (vaultCreditFlow isDeposit) (R := R) hcode hd hdec hbody hretTy hprefix (by omega)
    (by simpa only [hentryPc] using h) ?_
  intro aw0 k0 C0 hperm rdBody
  rw [hbodyPc] at rdBody
  have hargs : evalExprs? config {contract := contract, locals := locals}
      (vaultSetLock (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1⟩)
      [.var (if isDeposit then "_assets" else "_shares"), .var "_receiver"] =
      .ok [.int (Int.ofNat (calldataWord I.calldata 4).toNat), .address (AccountAddress.ofNat receiver.toNat)] := by
    simp only [evalExprs?, evalExpr?, ha, hr, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rcases vaultCreditRoutine isDeposit SourceState.init hsize hmr hcanon hperm hstack rdBody with
    ⟨evm1, σ1, locals1, value, hcallee, hs1, hret⟩ | ⟨hcallee, hrev⟩
  · exact Or.inl ⟨evm1, σ1, value, internalCallFunctionReturn (callee := vaultCreditFunction isDeposit)
      hargs (by cases isDeposit <;> rfl) (by cases isDeposit <;> rfl) hcallee, hs1, hret⟩
  · exact Or.inr ⟨internalCallFunctionRevert (callee := vaultCreditFunction isDeposit)
      hargs (by cases isDeposit <;> rfl) (by cases isDeposit <;> rfl) hcallee, hrev⟩

end Benchmarks.CurveVault

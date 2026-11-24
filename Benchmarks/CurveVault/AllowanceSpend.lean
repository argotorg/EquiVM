import Benchmarks.CurveVault.AllowanceSpendEVM
import Benchmarks.CurveVault.ApproveInternal
import Benchmarks.CurveVault.AddressWord

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultAllowanceSpend (flow : VaultAllowanceSpendFlow) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner old value : UInt256} {R : List UInt256} {locals : Store}
    {ownerExpr oldExpr valueExpr : Expr} {retVar : Ident}
    (hs : SourceState s0 I σ evm) (hsize : flow.allowanceOffset + 32 ≤ mem.size)
    (hmo : memLoad (UInt256.ofNat flow.ownerOffset) mem = owner)
    (hma : memLoad (UInt256.ofNat flow.allowanceOffset) mem = old)
    (hmv : flow.amount I mem = value) (hcanon : owner.toNat < EVM.addressModulus)
    (ho : evalExpr? config {contract := contract, locals := locals} evm ownerExpr =
      .ok (.address (AccountAddress.ofNat owner.toNat)))
    (ha : evalExpr? config {contract := contract, locals := locals} evm oldExpr = .ok (.int (Int.ofNat old.toNat)))
    (hv : evalExpr? config {contract := contract, locals := locals} evm valueExpr = .ok (.int (Int.ofNat value.toNat)))
    (hperm : I.perm = true) (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat flow.entry) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (mem' : ByteArray) (aw' : UInt256) (k' C' : Nat),
      ExecStmt fork config {contract := contract, locals := locals} evm
        (.internalCall "_approve" [ownerExpr, .env .caller, sourceCheckedSub256 oldExpr valueExpr] retVar)
        (.ok {contract := contract, locals := locals.insert retVar .unit} evm') ∧
      SourceState s0 I σ' evm' ∧ WordMemoryRange mem mem' 192 UInt256.size ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat flow.next) R mem' aw' rdata σ' k' C') ∨
    (ExecStmt fork config {contract := contract, locals := locals} evm
      (.internalCall "_approve" [ownerExpr, .env .caller, sourceCheckedSub256 oldExpr valueExpr] retVar) .reverted ∧
      RDrev fork vaultBytecode g s0) := by
  rcases vaultAllowanceSpendEVM flow hsize hmo hma hmv (by omega) h with
    ⟨hsub, aw0, k0, C0, rdApprove⟩ | ⟨hlt, hrev⟩
  swap
  · refine Or.inr ⟨ExecStmt.internalCallArgsRevert ?_, hrev⟩
    simp only [evalExprs?, ho, evalExpr_checkedSub256_revert ha hv hlt,
      evalExpr?, envValue, EvalResult.bind, pure, bind]
  let spender := UInt256.ofNat I.source.val
  obtain ⟨hargsSize, howner, hspender, hvalue⟩ := vaultApproveArguments_reads mem owner spender (UInt256.sub old value)
  obtain ⟨evm', σ', aw', k', C', hcallee, hs', rdNext⟩ := vaultApproveRoutine hs hargsSize howner hspender hvalue
    hcanon (addressWord_canonical I.source) hperm (by omega) (by cases flow <;> native_decide) rdApprove
  dsimp only [spender] at hcallee
  rw [addressWord_roundtrip] at hcallee
  have hargs : evalExprs? config {contract := contract, locals := locals} evm
      [ownerExpr, .env .caller, sourceCheckedSub256 oldExpr valueExpr] =
      .ok [.address (AccountAddress.ofNat owner.toNat), .address I.source, .int (Int.ofNat (UInt256.sub old value).toNat)] := by
    simp only [evalExprs?, ho, evalExpr_checkedSub256_ok ha hv rfl hsub,
      evalExpr?, envValue, hs.env, EvalResult.bind, pure, bind]
  refine Or.inl ⟨evm', σ', _, aw', k', C',
    internalCallFunctionReturn (callee := vaultApproveFunction) hargs rfl rfl hcallee, hs', ?_, rdNext⟩
  exact ((vaultApproveArguments_frame mem owner spender (UInt256.sub old value)).mono (by omega) (le_refl _)).trans
    (vaultApproveMemory_frame _ owner spender (UInt256.sub old value))

end Benchmarks.CurveVault

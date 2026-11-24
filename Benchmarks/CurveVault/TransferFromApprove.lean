import Benchmarks.CurveVault.TransferFromTail
import Benchmarks.CurveVault.AllowanceSpend

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

abbrev vaultTransferFromApproveStmt : Stmt := .internalCall "_approve"
  [.var "_from", .env .caller, sourceCheckedSub256 (.var "allowance_") (.var "_value")] "__c0"

theorem vaultTransferFromApprove {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {sender old : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 288 ≤ mem.size)
    (hmf : memLoad (UInt256.ofNat 192) mem = sender)
    (hma : memLoad (UInt256.ofNat 256) mem = old)
    (hcanon : sender.toNat < EVM.addressModulus)
    (hf : locals.get? "_from" = some (.address (AccountAddress.ofNat sender.toNat)))
    (ha : locals.get? "allowance_" = some (.int (Int.ofNat old.toNat)))
    (hv : locals.get? "_value" = some (.int (Int.ofNat (calldataWord I.calldata 68).toNat)))
    (hperm : I.perm = true) (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 5804) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (mem' : ByteArray) (aw' : UInt256) (k' C' : Nat),
      ExecStmt fork config {contract := contract, locals := locals} evm vaultTransferFromApproveStmt
        (.ok {contract := contract, locals := locals.insert "__c0" .unit} evm') ∧
      SourceState s0 I σ' evm' ∧ WordMemoryRange mem mem' 192 UInt256.size ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat 5845) R mem' aw' rdata σ' k' C') ∨
    (ExecStmt fork config {contract := contract, locals := locals} evm vaultTransferFromApproveStmt .reverted ∧
      RDrev fork vaultBytecode g s0) := by
  exact vaultAllowanceSpend .transferFrom hs hsize hmf hma rfl hcanon
    (by rw [evalExpr?]; simp only [hf, EvalResult.ofOption])
    (evalExpr_varUInt256 ha) (evalExpr_varUInt256 hv) hperm hstack h

end Benchmarks.CurveVault

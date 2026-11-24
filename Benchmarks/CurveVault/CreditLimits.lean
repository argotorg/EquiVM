import Benchmarks.CurveVault.CreditLimitsEVM
import Benchmarks.CurveVault.CreditSource
import Benchmarks.CurveVault.Storage

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultCreditLimitsBody (isDeposit : Bool) : List Stmt :=
  [.require (.binary .ge (sourceAdd256 (.var "total_assets") (.var (vaultCreditAssetsName isDeposit))) (.intLit 10000)),
    .letDecl "max_supply" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.storage {base := "maxSupply", steps := []}),
    .require (.binary .le (sourceAdd256 (.var "total_assets") (.var (vaultCreditAssetsName isDeposit))) (.var "max_supply"))]

theorem vaultCreditLimits (isDeposit : Bool) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {total assets : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm)
    (ht : locals.get? "total_assets" = some (.int (Int.ofNat total.toNat)))
    (ha : locals.get? (vaultCreditAssetsName isDeposit) = some (.int (Int.ofNat assets.toNat)))
    (hb : locals.get? "maxSupply" = none)
    (hmt : memLoad (UInt256.ofNat 640) (vaultCreditLimitsMemory isDeposit mem) = total)
    (hma : vaultCreditLimitsAssets isDeposit I (vaultCreditLimitsMemory isDeposit mem) = assets)
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat (vaultCreditLimitsEntry isDeposit)) R mem aw rdata σ k C) :
    (∃ aw' k' C',
      ExecBlock fork config {contract := contract, locals := locals} evm (vaultCreditLimitsBody isDeposit)
        (.ok {contract := contract, locals := (locals.insert "max_supply"
          (.int (Int.ofNat (codeOwnerStorageWord I σ ⟨5⟩).toNat)))} evm) ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat (vaultCreditLimitsNext isDeposit)) R
        (vaultCreditLimitsMemory isDeposit mem) aw' rdata σ k' C') ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm (vaultCreditLimitsBody isDeposit)
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  let limit := codeOwnerStorageWord I σ ⟨5⟩
  let locals1 := locals.insert "max_supply" (.int (Int.ofNat limit.toNat))
  have htEval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) ht
  have haEval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) ha
  have hconstant : evalExpr? config {contract := contract, locals := locals} evm (.intLit 10000) =
      .ok (.int (Int.ofNat (UInt256.ofNat 10000).toNat)) := by rw [evalExpr?]; rfl
  have hlimit : evalExpr? config {contract := contract, locals := locals} evm
      (.storage {base := "maxSupply", steps := []}) = .ok (.int (Int.ofNat limit.toNat)) := by
    simpa only [wordToElem, normalizeInt_uint256_word, hs.storageRead] using
      vaultEvalScalar evm locals "maxSupply" (.int (.uint ⟨256, by decide⟩)) ⟨5⟩ hb rfl rfl
  have htEval1 := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm)
    (show locals1.get? "total_assets" = _ from by rw [store_get_ne _ _ (by decide +kernel), ht])
  have haEval1 := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm)
    (show locals1.get? (vaultCreditAssetsName isDeposit) = _ from by
      rw [store_get_ne _ _ (by cases isDeposit <;> decide +kernel), ha])
  have hlEval1 := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm)
    (show locals1.get? "max_supply" = _ from store_get_self _ _ _)
  rcases vaultCreditLimitsEVM isDeposit hmt hma hstack h with
    ⟨hfit, hmin, hmax, aw', k', C', rd⟩ | ⟨hover, hrev⟩ | ⟨hfit, hmin, hrev⟩ | ⟨hfit, hmin, hmax, hrev⟩
  · refine Or.inl ⟨aw', k', C', ?_, rd⟩
    exact ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_ge_uint256_true
      (evalExpr_add256_ok htEval haEval rfl hfit) hconstant hmin))
      (ExecBlock.consNormal (ExecStmt.letDecl hlimit)
        (ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_le_uint256_true
          (evalExpr_add256_ok htEval1 haEval1 rfl hfit) hlEval1 hmax)) ExecBlock.nil))
  · refine Or.inr ⟨ExecBlock.consRevert (ExecStmt.requireRevert ?_), hrev⟩
    have hsum := evalExpr_add256_revert htEval haEval hover
    rw [evalExpr_binary_nonshort (by decide +kernel) (by decide +kernel)]
    simp only [hsum, EvalResult.bind, bind]
  · exact Or.inr ⟨ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_ge_uint256_false
      (evalExpr_add256_ok htEval haEval rfl hfit) hconstant hmin)), hrev⟩
  · exact Or.inr ⟨ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_ge_uint256_true
      (evalExpr_add256_ok htEval haEval rfl hfit) hconstant hmin))
      (ExecBlock.consNormal (ExecStmt.letDecl hlimit) (ExecBlock.consRevert (ExecStmt.requireFalse
        (evalExpr_le_uint256_false (evalExpr_add256_ok htEval1 haEval1 rfl hfit) hlEval1 hmax)))), hrev⟩

end Benchmarks.CurveVault

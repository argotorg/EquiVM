import Benchmarks.CurveVault.DebitMinimumEVM
import Benchmarks.CurveVault.DebitSource

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultDebitMinimumExpr (isWithdraw : Bool) : Expr :=
  .binary .or
    (.binary .ge (sourceCheckedSub256 (.var "total_assets") (.var (vaultDebitAssetsName isWithdraw))) (.intLit 10000))
    (.binary .eq (.var "total_assets") (.var (vaultDebitAssetsName isWithdraw)))

theorem vaultDebitMinimum (isWithdraw : Bool) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {total assets : UInt256} {R : List UInt256} {locals : Store}
    (ht : locals.get? "total_assets" = some (.int (Int.ofNat total.toNat)))
    (ha : locals.get? (vaultDebitAssetsName isWithdraw) = some (.int (Int.ofNat assets.toNat)))
    (hmt : memLoad (UInt256.ofNat 640) (vaultDebitMinimumMemory isWithdraw mem) = total)
    (hma : vaultDebitMinimumAssets isWithdraw I (vaultDebitMinimumMemory isWithdraw mem) = assets)
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat (vaultDebitMinimumEntry isWithdraw)) R mem aw rdata σ k C) :
    (∃ aw' k' C',
      ExecStmt fork config {contract := contract, locals := locals} evm (.require (vaultDebitMinimumExpr isWithdraw))
        (.ok {contract := contract, locals := locals} evm) ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat (vaultDebitMinimumNext isWithdraw)) R
        (vaultDebitMinimumMemory isWithdraw mem) aw' rdata σ k' C') ∨
    (ExecStmt fork config {contract := contract, locals := locals} evm (.require (vaultDebitMinimumExpr isWithdraw))
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  have htEval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) ht
  have haEval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) ha
  have hconstant : evalExpr? config {contract := contract, locals := locals} evm (.intLit 10000) =
      .ok (.int (Int.ofNat (UInt256.ofNat 10000).toNat)) := by rw [evalExpr?]; rfl
  rcases vaultDebitMinimumEVM isWithdraw hmt hma hstack h with
    ⟨hsub, haccept, aw', k', C', rd⟩ | ⟨hlt, hrev⟩ | ⟨hsub, hlt, hne, hrev⟩
  · refine Or.inl ⟨aw', k', C', ExecStmt.requireTrue ?_, rd⟩
    have hsubEval := evalExpr_checkedSub256_ok htEval haEval rfl hsub
    by_cases hmin : 10000 ≤ (UInt256.sub total assets).toNat
    · exact evalExpr_or_true_left (evalExpr_ge_uint256_true hsubEval hconstant hmin)
    · have heq : total = assets := haccept.resolve_left hmin
      exact evalExpr_or_false_right (evalExpr_ge_uint256_false hsubEval hconstant (by exact Nat.lt_of_not_ge hmin))
        (evalExpr_eq_int_true htEval haEval (by rw [heq]))
  · refine Or.inr ⟨ExecStmt.requireRevert ?_, hrev⟩
    have hleft : evalExpr? config {contract := contract, locals := locals} evm
        (.binary .ge (sourceCheckedSub256 (.var "total_assets") (.var (vaultDebitAssetsName isWithdraw))) (.intLit 10000)) =
        .revert := by
      rw [evalExpr_binary_nonshort (by decide +kernel) (by decide +kernel)]
      simp only [evalExpr_checkedSub256_revert htEval haEval hlt, EvalResult.bind, bind]
    rw [vaultDebitMinimumExpr, evalExpr?]
    simp only [hleft, EvalResult.bind, bind]
  · exact Or.inr ⟨ExecStmt.requireFalse (evalExpr_or_false_right
      (evalExpr_ge_uint256_false (evalExpr_checkedSub256_ok htEval haEval rfl hsub) hconstant hlt)
      (evalExpr_eq_int_false htEval haEval (fun hn => hne (u256_inj (Int.ofNat.inj hn))))), hrev⟩

end Benchmarks.CurveVault

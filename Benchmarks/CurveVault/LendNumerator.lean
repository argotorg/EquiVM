import Benchmarks.CurveVault.Arithmetic
import Benchmarks.CurveVault.LendAmmCall

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

abbrev vaultLendFunction : FunctionDecl := contract.functions[2]!
abbrev vaultLendNumeratorStmt : Stmt := vaultLendFunction.body[4]!

theorem vaultLendNumerator {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {rate debt unused : UInt256} {R : List UInt256} {locals : Store}
    (hr : locals.get? "__c1" = some (.int (Int.ofNat rate.toNat)))
    (hd : locals.get? "debt" = some (.int (Int.ofNat debt.toNat)))
    (hmr : memLoad (UInt256.ofNat 320) mem = rate)
    (hmd : memLoad (UInt256.ofNat 256) mem = debt) (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 1240) (unused :: R) mem aw rdata σ k C) :
    let yearly := UInt256.mul rate (UInt256.ofNat 31536000)
    let numerator := UInt256.mul yearly debt
    (∃ aw' k' C',
      ExecStmt fork config {contract := contract, locals := locals} evm vaultLendNumeratorStmt
        (.ok {contract := contract, locals := locals.insert "numerator" (.int (Int.ofNat numerator.toNat))} evm) ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat 1288) (numerator :: debt :: yearly :: R) mem aw' rdata σ k' C') ∨
    (ExecStmt fork config {contract := contract, locals := locals} evm vaultLendNumeratorStmt .reverted ∧ RDrev fork vaultBytecode g s0) := by
  dsimp only
  have hrEval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) hr
  have hdEval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) hd
  have hyEval : evalExpr? config {contract := contract, locals := locals} evm (.intLit 31536000) =
      .ok (.int (Int.ofNat (UInt256.ofNat 31536000).toNat)) := by simp [evalExpr?, pure]; rfl
  by_cases hyear : rate.toNat * (UInt256.ofNat 31536000).toNat < UInt256.size
  swap
  · have hover : UInt256.size ≤ rate.toNat * (UInt256.ofNat 31536000).toNat := by omega
    have rdFail := vaultBlocks.vault_block_1240_taken (by omega)
      (by rw [hmr]; exact u256_xor_ne_zero_of_ne (u256_mul_div_right_overflow_ne _ _ hover)) (by native_decide) h
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_1240_taken_stack, List.length_cons]; omega) rdFail
    exact Or.inr ⟨ExecStmt.letDeclRevert (evalExpr_checked_binary_left_revert .mul _
      (evalExpr_mul256_revert hrEval hyEval hover)), hrev⟩
  have rd1266 := vaultBlocks.vault_block_1240_fallthrough (by omega)
    (by rw [hmr, u256_mul_div_right_eq_of_noOverflow _ _ (by decide +kernel) hyear, u256_xor_self]; rfl) h
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 1266)
    (UInt256.mul (memLoad (UInt256.ofNat 320) mem) (UInt256.ofNat 31536000) :: memLoad (UInt256.ofNat 320) mem :: R)
    mem _ rdata σ _ _ at rd1266
  rw [hmr] at rd1266
  have hyearEval := evalExpr_mul256_ok hrEval hyEval rfl hyear
  by_cases hnum : (UInt256.mul rate (UInt256.ofNat 31536000)).toNat * debt.toNat < UInt256.size
  · have rd1288 := vaultBlocks.vault_block_1266_fallthrough hstack (by rw [hmd]; exact mulCheck_ok _ _ hnum) rd1266
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 1288)
      (UInt256.mul (UInt256.mul rate (UInt256.ofNat 31536000)) (memLoad (UInt256.ofNat 256) mem) ::
        memLoad (UInt256.ofNat 256) mem :: UInt256.mul rate (UInt256.ofNat 31536000) :: R) mem _ rdata σ _ _ at rd1288
    rw [hmd] at rd1288
    exact Or.inl ⟨_, _, _, ExecStmt.letDecl (evalExpr_mul256_ok hyearEval hdEval rfl hnum), rd1288⟩
  · have hover : UInt256.size ≤ (UInt256.mul rate (UInt256.ofNat 31536000)).toNat * debt.toNat := by omega
    have rdFail := vaultBlocks.vault_block_1266_taken hstack (by rw [hmd]; exact mulCheck_overflow _ _ hover)
      (by native_decide) rd1266
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_1266_taken_stack, List.length_cons]; omega) rdFail
    exact Or.inr ⟨ExecStmt.letDeclRevert (evalExpr_mul256_revert hyearEval hdEval hover), hrev⟩
end Benchmarks.CurveVault

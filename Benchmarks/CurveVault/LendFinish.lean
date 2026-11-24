import Benchmarks.CurveVault.LendNumerator
import Benchmarks.CurveVault.Memory
import Benchmarks.CurveVault.RuntimeBlocks_007

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

abbrev vaultLendReturnStmt : Stmt := vaultLendFunction.body[9]!
abbrev vaultLendScale : UInt256 := UInt256.ofNat 1000000000000000000

theorem vaultLendFinish {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {gross pct unused : UInt256} {R : List UInt256} {locals : Store}
    (hsize : 320 ≤ mem.size)
    (hg : locals.get? "gross_apr" = some (.int (Int.ofNat gross.toNat)))
    (hp : locals.get? "admin_pct" = some (.int (Int.ofNat pct.toNat)))
    (hmg : memLoad (UInt256.ofNat 288) mem = gross)
    (hmp : memLoad (UInt256.ofNat 352) mem = pct) (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 1369) (unused :: R) mem aw rdata σ k C) :
    let result := UInt256.div (UInt256.mul gross (UInt256.sub vaultLendScale pct)) vaultLendScale
    (ExecStmt fork config {contract := contract, locals := locals} evm vaultLendReturnStmt
      (.returned {contract := contract, locals := locals} evm (some [.int (Int.ofNat result.toNat)])) ∧
      RDret fork vaultBytecode g s0 σ result.toByteArray) ∨
    (ExecStmt fork config {contract := contract, locals := locals} evm vaultLendReturnStmt .reverted ∧ RDrev fork vaultBytecode g s0) := by
  dsimp only
  let mem1 := pct.toByteArray.write 0 mem 320 32
  have hgap : 320 - mem.size < USize.size := lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 320 (by norm_num))
  have hp1 : memLoad (UInt256.ofNat 320) mem1 = pct := memLoad_write_back _ _ 320 (by decide +kernel) hgap
  have hg1 : memLoad (UInt256.ofNat 288) mem1 = gross := by
    rw [memLoad_below_write _ _ 320 288 hsize (by omega) hgap (by decide +kernel), hmg]
  have hgEval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) hg
  have hpEval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) hp
  have hscale : evalExpr? config {contract := contract, locals := locals} evm (.intLit 1000000000000000000) =
      .ok (.int (Int.ofNat vaultLendScale.toNat)) := by simp [evalExpr?, pure]; rfl
  by_cases hsub : pct.toNat ≤ vaultLendScale.toNat
  swap
  · have hlt : vaultLendScale.toNat < pct.toNat := by omega
    have rdFail := vaultBlocks.vault_block_1369_taken (by omega)
      (by rw [hmp]; change UInt256.gt (UInt256.sub vaultLendScale (memLoad (UInt256.ofNat 320) mem1)) vaultLendScale ≠ _
          rw [hp1, u256_sub_underflow_gt _ _ hlt]
          decide +kernel) (by native_decide) h
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_1369_taken_stack, List.length_cons]; omega) rdFail
    refine Or.inr ⟨ExecStmt.returnRevert ?_, hrev⟩
    have heval := evalExpr_checked_mul_right_revert (.uint ⟨256, by decide⟩) hgEval (evalExpr_checkedSub256_revert hscale hpEval hlt)
    rw [evalExprs?, evalExpr_binary_revert_left (by decide +kernel) (by decide +kernel) heval]
    rfl
  have rd1413 := vaultBlocks.vault_block_1369_fallthrough (by omega)
    (by rw [hmp]; change UInt256.gt (UInt256.sub vaultLendScale (memLoad (UInt256.ofNat 320) mem1)) vaultLendScale = _
        rw [hp1]; exact ugt_zero (by rw [usub_toNat hsub]; omega)) h
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 1413)
    (UInt256.sub vaultLendScale (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem 320 32)) ::
      memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem 320 32) ::
      memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem 320 32) :: R)
      ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem 320 32) _ rdata σ _ _ at rd1413
  rw [hmp, hp1, hg1] at rd1413
  have hsubEval := evalExpr_checkedSub256_ok hscale hpEval rfl hsub
  by_cases hmul : gross.toNat * (UInt256.sub vaultLendScale pct).toNat < UInt256.size
  · have rd1431 := vaultBlocks.vault_block_1413_fallthrough hstack (mulCheck_ok _ _ hmul) rd1413
    have rd1457 := vaultBlocks.vault_block_1431 (by omega) rd1431
    have hret := vaultBlocks.vault_block_1457 (by omega) rd1457
    change RDret fork vaultBytecode g s0 σ
      (((UInt256.div (UInt256.mul gross (UInt256.sub vaultLendScale pct)) vaultLendScale).toByteArray.write
        0 mem1 352 32).readWithPadding 352 32) at hret
    rw [toByteArray_write_read_back_of_gap _ _ _ (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 352 (by norm_num)))] at hret
    exact Or.inl ⟨ExecStmt.return (evalExprs?_singleton (evalExpr_div_uint256_ok
      (evalExpr_mul256_ok hgEval hsubEval rfl hmul) hscale (by decide +kernel) rfl)), hret⟩
  · have hover : UInt256.size ≤ gross.toNat * (UInt256.sub vaultLendScale pct).toNat := by omega
    have rdFail := vaultBlocks.vault_block_1413_taken hstack (mulCheck_overflow _ _ hover) (by native_decide) rd1413
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_1413_taken_stack, List.length_cons]; omega) rdFail
    refine Or.inr ⟨ExecStmt.returnRevert ?_, hrev⟩
    rw [evalExprs?, evalExpr_binary_revert_left (by decide +kernel) (by decide +kernel) (evalExpr_mul256_revert hgEval hsubEval hover)]
    rfl
end Benchmarks.CurveVault

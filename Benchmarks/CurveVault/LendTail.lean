import Benchmarks.CurveVault.LendFinish
import Benchmarks.CurveVault.LendControllerCalls
import Benchmarks.CurveVault.TotalAssetsInternal

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

abbrev vaultLendTailBody : List Stmt := vaultLendFunction.body.drop 5

theorem vaultLendTail {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {numerator unused unused2 : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hbase : locals.get? "_controller" = none)
    (hnum : locals.get? "numerator" = some (.int (Int.ofNat numerator.toNat)))
    (hstack : R.length + 11 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 1288) (numerator :: unused :: unused2 :: R) mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (value : UInt256),
      ExecBlock fork config {contract := contract, locals := locals} evm vaultLendTailBody
        (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat value.toNat)])) ∧
      SourceState s0 I σ' evm' ∧ RDret fork vaultBytecode g s0 σ' value.toByteArray) ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm vaultLendTailBody .reverted ∧ RDrev fork vaultBytecode g s0) := by
  have hgap (d : Nat) (hd : d < 1024) (m : ByteArray) : d - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize d (by omega))
  have rd6772 := vaultBlocks.vault_block_1288 (by omega) (by native_decide) h
  rcases vaultTotalAssetsRoutine hs (by simp only [List.length_cons]; omega) (by native_decide) rd6772 with
    ⟨evm0, σ0, calleeLocals, a, b, c, aw0, out0, k0, C0, hcallee, hs0, rd1302⟩ | ⟨hcallee, hrev⟩
  swap
  · exact Or.inr ⟨ExecBlock.consRevert (internalCallFunctionRevert (callee := vaultTotalAssetsFunction)
      (argVals := []) (by simp [evalExprs?, pure]) rfl rfl hcallee), hrev⟩
  let total := UInt256.sub (a + b) c
  let locals0 := locals.insert "__c2" (.int (Int.ofNat total.toNat))
  let mem0 := total.toByteArray.write 0 (vaultTotalAssetsScratch mem a b c) 384 32
  have hsize0 : 416 ≤ mem0.size := toByteArray_write_size_ge_off_add32 _ _ 384 (hgap _ (by omega) _)
  have hword : memLoad (UInt256.ofNat 384) mem0 = total := memLoad_write_back _ _ 384 (by decide +kernel) (hgap _ (by omega) _)
  have hcall := internalCallFunctionReturn (caller := {contract := contract, locals := locals})
    (callee := vaultTotalAssetsFunction) (name := "_total_assets") (args := []) (argVals := []) (retVar := "__c2")
    (by simp [evalExprs?, pure]) rfl rfl hcallee
  have hnEval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm0)
    (show locals0.get? "numerator" = some (.int (Int.ofNat numerator.toNat)) by
      rw [store_get_ne _ _ (by decide +kernel)]; exact hnum)
  have htEval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm0)
    (show locals0.get? "__c2" = some (.int (Int.ofNat total.toNat)) by simp [locals0])
  by_cases hz : total = ⟨0⟩
  · have rdFail := vaultBlocks.vault_block_1302_taken (by simp only [List.length_cons]; omega)
      (by change UInt256.isZero (memLoad (UInt256.ofNat 384) mem0) ≠ _; rw [hword, hz]; decide +kernel) (by native_decide) rd1302
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_1302_taken_stack, List.length_cons]; omega) rdFail
    refine Or.inr ⟨ExecBlock.consNormal hcall (ExecBlock.consRevert (ExecStmt.letDeclRevert ?_)), hrev⟩
    change evalExpr? config {contract := contract, locals := locals0} evm0
      (.binary .div (.var "numerator") (.var "__c2")) = .revert
    rw [evalExpr_binary_nonshort (by decide +kernel) (by decide +kernel)]
    simp only [hnEval, htEval, bind, EvalResult.bind, evalBinaryOp?, hz]
    rfl
  have rd1313 := vaultBlocks.vault_block_1302_fallthrough (by simp only [List.length_cons]; omega)
    (by change UInt256.isZero (memLoad (UInt256.ofNat 384) mem0) = _; rw [hword]; exact isZero_eq_zero_of_ne hz) rd1302
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 1313) (memLoad (UInt256.ofNat 384) mem0 :: numerator :: R)
    mem0 _ out0 σ0 _ _ at rd1313
  rw [hword] at rd1313
  let gross := UInt256.div numerator total
  let locals1 := locals0.insert "gross_apr" (.int (Int.ofNat gross.toNat))
  have hgEval := evalExpr_div_uint256_ok hnEval htEval hz rfl
  rcases vaultLendAdminCall (locals := locals1) hs0
    (by rw [store_get_ne _ _ (by decide +kernel), store_get_ne _ _ (by decide +kernel)]; exact hbase)
    (by omega) rd1313 with
    ⟨evm1, σ1, out1, aw1, k1, C1, _, _, hadmin, hs1, rd1369⟩ | ⟨hadmin, hrev⟩
  swap
  · refine Or.inr ⟨ExecBlock.consNormal hcall (ExecBlock.consNormal (ExecStmt.letDecl hgEval) ?_), hrev⟩
    change ExecBlock fork _ _ _ (vaultControllerCall "controller_admin_percentage" "admin_pct" "admin_percentage" ++ [vaultLendReturnStmt]) _
    exact execBlock_reverted_append hadmin
  let pct := retWord out1
  let grossMem := gross.toByteArray.write 0 mem0 288 32
  let selectorMem := (UInt256.ofNat 274332861).toByteArray.write 0 grossMem 352 32
  let mem1 := pct.toByteArray.write 0 selectorMem 352 32
  let locals2 := vaultControllerCallLocals locals1 evm0 "controller_admin_percentage" "admin_pct" (.int (Int.ofNat pct.toNat))
  have hsizeGross : 320 ≤ grossMem.size := toByteArray_write_size_ge_off_add32 _ _ 288 (hgap _ (by omega) _)
  have hsizeSelector : 384 ≤ selectorMem.size := toByteArray_write_size_ge_off_add32 _ _ 352 (hgap _ (by omega) _)
  have hsize1 : 384 ≤ mem1.size := toByteArray_write_size_ge_off_add32 _ _ 352 (hgap _ (by omega) _)
  have hp1 : memLoad (UInt256.ofNat 352) mem1 = pct := memLoad_write_back _ _ 352 (by decide +kernel) (hgap _ (by omega) _)
  have hg1 : memLoad (UInt256.ofNat 288) mem1 = gross := by
    rw [memLoad_below_write _ _ 352 288 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel),
      memLoad_below_write _ _ 352 288 hsizeGross (by omega) (hgap _ (by omega) _) (by decide +kernel)]
    exact memLoad_write_back _ _ 288 (by decide +kernel) (hgap _ (by omega) _)
  have hgloc : locals2.get? "gross_apr" = some (.int (Int.ofNat gross.toNat)) := by
    simp only [locals2, vaultControllerCallLocals, locals1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl
  have hploc : locals2.get? "admin_pct" = some (.int (Int.ofNat pct.toNat)) := store_get_self _ _ _
  rcases vaultLendFinish (evm := evm1) (locals := locals2) (by omega) hgloc hploc hg1 hp1 (by omega) rd1369 with
    ⟨hfinish, hret⟩ | ⟨hfinish, hrev⟩
  · refine Or.inl ⟨evm1, σ1, locals2, UInt256.div (UInt256.mul gross (UInt256.sub vaultLendScale pct)) vaultLendScale,
      ExecBlock.consNormal hcall (ExecBlock.consNormal (ExecStmt.letDecl hgEval) ?_), hs1, hret⟩
    change ExecBlock fork _ _ _ (vaultControllerCall "controller_admin_percentage" "admin_pct" "admin_percentage" ++ [vaultLendReturnStmt]) _
    exact execBlock_append hadmin (ExecBlock.consReturn hfinish)
  · refine Or.inr ⟨ExecBlock.consNormal hcall (ExecBlock.consNormal (ExecStmt.letDecl hgEval) ?_), hrev⟩
    change ExecBlock fork _ _ _ (vaultControllerCall "controller_admin_percentage" "admin_pct" "admin_percentage" ++ [vaultLendReturnStmt]) _
    exact execBlock_append hadmin (ExecBlock.consRevert hfinish)
end Benchmarks.CurveVault

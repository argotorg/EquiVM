import Benchmarks.CurveVault.LendTail

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

theorem vaultLendBody_eq : vaultLendFunction.body =
    vaultControllerCall "controller_total_debt" "debt" "total_debt" ++ vaultLendFunction.body.drop 2 := rfl

theorem vaultLendRoutine {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (hs : SourceState s0 I σ evm) (hstack : R.length + 11 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 1117) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (value : UInt256),
      ExecFuncBody fork config {contract := contract, locals := ∅} evm vaultLendFunction.body
        (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat value.toNat)])) ∧
      SourceState s0 I σ' evm' ∧ RDret fork vaultBytecode g s0 σ' value.toByteArray) ∨
    (ExecFuncBody fork config {contract := contract, locals := ∅} evm vaultLendFunction.body .reverted ∧
      RDrev fork vaultBytecode g s0) := by
  have hgap (d : Nat) (hd : d < 1024) (m : ByteArray) : d - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize d (by omega))
  rcases vaultLendDebtCall (locals := ∅) hs (by simp) (by omega) h with
    ⟨evm0, σ0, out0, aw0, k0, C0, _, _, hdebtCall, hs0, rd1162⟩ | ⟨hdebtCall, hrev⟩
  swap
  · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [vaultLendBody_eq]
    exact execBlock_reverted_append hdebtCall
  let debt := retWord out0
  let locals0 := vaultControllerCallLocals ∅ evm "controller_total_debt" "debt" (.int (Int.ofNat debt.toNat))
  let mem0 := debt.toByteArray.write 0 (vaultBlocks.vault_block_1117_memory (mem := mem)) 288 32
  let mem1 := debt.toByteArray.write 0 mem0 256 32
  have hd0 : memLoad (UInt256.ofNat 288) mem0 = debt := memLoad_write_back _ _ 288 (by decide +kernel) (hgap _ (by omega) _)
  have hd1 : memLoad (UInt256.ofNat 256) mem1 = debt := memLoad_write_back _ _ 256 (by decide +kernel) (hgap _ (by omega) _)
  have hsize1 : 288 ≤ mem1.size := toByteArray_write_size_ge_off_add32 _ _ 256 (hgap _ (by omega) _)
  have hdEval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm0)
    (show locals0.get? "debt" = some (.int (Int.ofNat debt.toNat)) by simp [locals0, vaultControllerCallLocals])
  by_cases hz : debt = ⟨0⟩
  · have rd1180 := vaultBlocks.vault_block_1162_fallthrough (by omega)
      (by change memLoad (UInt256.ofNat 256) ((memLoad (UInt256.ofNat 288) mem0).toByteArray.write 0 mem0 256 32) = _
          rw [hd0, hd1, hz]; rfl) rd1162
    have rd1457 := vaultBlocks.vault_block_1180 (by simp only [vaultBlocks.vault_block_1162_fallthrough_stack]; omega)
      (by native_decide) rd1180
    have hret := vaultBlocks.vault_block_1457 (by simp only [vaultBlocks.vault_block_1162_fallthrough_stack]; omega) rd1457
    change RDret fork vaultBytecode g s0 σ0
      (((⟨0⟩ : UInt256).toByteArray.write 0 _ 288 32).readWithPadding 288 32) at hret
    rw [toByteArray_write_read_back_of_gap _ _ _ (hgap _ (by omega) _)] at hret
    refine Or.inl ⟨evm0, σ0, locals0, ⟨0⟩, ExecFuncBody.execBlockRet ?_, hs0, hret⟩
    rw [vaultLendBody_eq]
    apply execBlock_append hdebtCall
    apply ExecBlock.consReturn (ExecStmt.iteTrue ?_ ?_)
    · exact evalExpr_eq_int_true (b := 0) hdEval (by simp [evalExpr?, pure]) (by rw [hz]; rfl)
    · exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExprs?, evalExpr?, pure, bind, EvalResult.bind]))
  have hfalse : evalExpr? config {contract := contract, locals := locals0} evm0
      (.binary .eq (.var "debt") (.intLit 0)) = .ok (.bool false) :=
    evalExpr_eq_int_false (b := 0) hdEval (by simp [evalExpr?, pure])
      (fun hn => hz (uint256_toNat_eq_zero (Int.ofNat.inj hn)))
  have rd1194 := vaultBlocks.vault_block_1162_taken (by omega)
    (by change memLoad (UInt256.ofNat 256) ((memLoad (UInt256.ofNat 288) mem0).toByteArray.write 0 mem0 256 32) ≠ _
        rw [hd0, hd1]; exact hz) (by native_decide) rd1162
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 1194) R
    ((memLoad (UInt256.ofNat 288) mem0).toByteArray.write 0 mem0 256 32) _ out0 σ0 _ _ at rd1194
  rw [hd0] at rd1194
  rcases vaultLendRateCall (locals := locals0) hs0 (by simp [locals0, vaultControllerCallLocals]) (by omega) rd1194 with
    ⟨evm1, σ1, out1, aw1, k1, C1, hrateCall, hs1, rd1240⟩ | ⟨hrateCall, hrev⟩
  swap
  · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [vaultLendBody_eq]
    exact execBlock_append hdebtCall (ExecBlock.consNormal (ExecStmt.iteFalse hfalse ExecBlock.nil)
      (ExecBlock.consRevert hrateCall))
  let rate := retWord out1
  let locals1 := locals0.insert "__c1" (.int (Int.ofNat rate.toNat))
  let selectorMem := (UInt256.ofNat 743338542).toByteArray.write 0 mem1 320 32
  let mem2 := rate.toByteArray.write 0 selectorMem 320 32
  have hsizeSelector : 352 ≤ selectorMem.size := toByteArray_write_size_ge_off_add32 _ _ 320 (hgap _ (by omega) _)
  have hr2 : memLoad (UInt256.ofNat 320) mem2 = rate := memLoad_write_back _ _ 320 (by decide +kernel) (hgap _ (by omega) _)
  have hd2 : memLoad (UInt256.ofNat 256) mem2 = debt := by
    rw [memLoad_below_write _ _ 320 256 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel),
      memLoad_below_write _ _ 320 256 hsize1 (by omega) (hgap _ (by omega) _) (by decide +kernel), hd1]
  rcases vaultLendNumerator (evm := evm1) (locals := locals1)
    (by simp [locals1]) (by rw [store_get_ne _ _ (by decide +kernel)]; exact store_get_self _ _ _) hr2 hd2 (by omega) rd1240 with
    ⟨aw2, k2, C2, hnum, rd1288⟩ | ⟨hnum, hrev⟩
  swap
  · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [vaultLendBody_eq]
    exact execBlock_append hdebtCall (ExecBlock.consNormal (ExecStmt.iteFalse hfalse ExecBlock.nil)
      (ExecBlock.consNormal hrateCall (ExecBlock.consRevert hnum)))
  let numerator := UInt256.mul (UInt256.mul rate (UInt256.ofNat 31536000)) debt
  let locals2 := locals1.insert "numerator" (.int (Int.ofNat numerator.toNat))
  have hprefix : ExecBlock fork config {contract := contract, locals := ∅} evm (vaultLendFunction.body.take 5)
      (.ok {contract := contract, locals := locals2} evm1) := by
    change ExecBlock fork _ _ _ (vaultControllerCall "controller_total_debt" "debt" "total_debt" ++
      (vaultLendFunction.body.drop 2).take 3) _
    exact execBlock_append hdebtCall (ExecBlock.consNormal (ExecStmt.iteFalse hfalse ExecBlock.nil)
      (ExecBlock.consNormal hrateCall (ExecBlock.consNormal hnum ExecBlock.nil)))
  have hbody : vaultLendFunction.body = vaultLendFunction.body.take 5 ++ vaultLendTailBody := rfl
  rcases vaultLendTail (locals := locals2) hs1
    (by simp [locals2, locals1, locals0, vaultControllerCallLocals]) (store_get_self _ _ _) hstack rd1288 with
    ⟨evm2, σ2, locals3, value, htail, hs2, hret⟩ | ⟨htail, hrev⟩
  · refine Or.inl ⟨evm2, σ2, locals3, value, ExecFuncBody.execBlockRet ?_, hs2, hret⟩
    rw [hbody]
    exact execBlock_append hprefix htail
  · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [hbody]
    exact execBlock_append hprefix htail
end Benchmarks.CurveVault

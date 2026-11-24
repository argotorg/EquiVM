import Benchmarks.CurveVault.PriceFinish
import Benchmarks.CurveVault.RuntimeBlocks_007

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultPriceRoutine {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {locals : Store} {isFloor : Bool}
    (hs : SourceState s0 I σ evm) (hsize : 352 ≤ mem.size)
    (hsupply : locals.get? "totalSupply" = none) (hprecision : locals.get? "precision" = none)
    (hflag : locals.get? "_is_floor" = some (.bool isFloor))
    (hmflag : memLoad (UInt256.ofNat 320) mem = if isFloor then ⟨1⟩ else ⟨0⟩)
    (hstack : R.length + 10 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 1543) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (value : UInt256),
      ExecFuncBody fork config {contract := contract, locals := locals} evm vaultPriceFunction.body
        (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat value.toNat)])) ∧
      SourceState s0 I σ' evm' ∧ RDret fork vaultBytecode g s0 σ' value.toByteArray) ∨
    (ExecFuncBody fork config {contract := contract, locals := locals} evm vaultPriceFunction.body .reverted ∧
      RDrev fork vaultBytecode g s0) := by
  let supply := codeOwnerStorageWord I σ ⟨14⟩
  let precision := codeOwnerStorageWord I σ ⟨15⟩
  let locals1 := locals.insert "supply" (.int (Int.ofNat supply.toNat))
  let mem1 := supply.toByteArray.write 0 mem 352 32
  have hgap (d : Nat) (hd : d < 1024) (m : ByteArray) : d - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize d (by omega))
  have hsize1 : 384 ≤ mem1.size := toByteArray_write_size_ge_off_add32 _ _ 352 (hgap _ (by omega) _)
  have hmSupply : memLoad (UInt256.ofNat 352) mem1 = supply := memLoad_write_back _ _ 352 (by decide +kernel) (hgap _ (by omega) _)
  have hsEval : evalExpr? config {contract := contract, locals := locals} evm
      (.storage {base := "totalSupply", steps := []}) = .ok (.int (Int.ofNat supply.toNat)) := by
    have hh := vaultEvalScalar evm locals "totalSupply" (.int (.uint ⟨256, by decide⟩)) ⟨14⟩ hsupply rfl rfl
    simpa only [wordToElem, normalizeInt_uint256_word, hs.storageRead] using hh
  have hsLocal := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm)
    (show locals1.get? "supply" = some (.int (Int.ofNat supply.toNat)) by simp [locals1])
  by_cases hz : supply = ⟨0⟩
  · obtain ⟨_, _, rd1558⟩ := vaultBlocks.vault_block_1543_fallthrough (by omega)
      (by change memLoad (UInt256.ofNat 352) mem1 = _; rw [hmSupply, hz]; rfl) h
    have rd1780 := vaultBlocks.vault_block_1558 (by omega) (by native_decide) rd1558
    have hret := vaultBlocks.vault_block_1780 (by omega) rd1780
    change RDret fork vaultBytecode g s0 σ
      (((UInt256.ofNat 1000000000000000).toByteArray.write 0 mem1 384 32).readWithPadding 384 32) at hret
    rw [toByteArray_write_read_back_of_gap _ _ _ (hgap _ (by omega) _)] at hret
    refine Or.inl ⟨evm, σ, locals1, UInt256.ofNat 1000000000000000, ?_, hs, hret⟩
    apply ExecFuncBody.execBlockRet
    apply ExecBlock.consNormal (ExecStmt.letDecl hsEval)
    apply ExecBlock.consReturn (ExecStmt.iteTrue ?_ ?_)
    · exact evalExpr_eq_int_true (b := 0) hsLocal (by simp [evalExpr?, pure]) (by rw [hz]; rfl)
    · apply ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
      simp only [evalExpr?, evalBinaryOp?, bind, pure, EvalResult.bind]
      rfl
  · have hfalse : evalExpr? config {contract := contract, locals := locals1} evm
        (.binary .eq (.var "supply") (.intLit 0)) = .ok (.bool false) :=
      evalExpr_eq_int_false hsLocal (by simp [evalExpr?, pure])
        (fun hn => hz (uint256_toNat_eq_zero (Int.ofNat.inj hn)))
    obtain ⟨_, _, rd1579⟩ := vaultBlocks.vault_block_1543_taken (by omega)
      (by change memLoad (UInt256.ofNat 352) mem1 ≠ _; rw [hmSupply]; exact hz) (by native_decide) h
    obtain ⟨_, _, rd6772⟩ := vaultBlocks.vault_block_1579 (by omega) (by native_decide) rd1579
    let mem2 := precision.toByteArray.write 0 mem1 384 32
    let locals2 := locals1.insert "precision_" (.int (Int.ofNat precision.toNat))
    have hsize2 : 416 ≤ mem2.size := toByteArray_write_size_ge_off_add32 _ _ 384 (hgap _ (by omega) _)
    have hpEval : evalExpr? config {contract := contract, locals := locals1} evm
        (.storage {base := "precision", steps := []}) = .ok (.int (Int.ofNat precision.toNat)) := by
      have hh := vaultEvalScalar evm locals1 "precision" (.int (.uint ⟨256, by decide⟩)) ⟨15⟩
        (by rw [store_get_ne _ _ (by decide +kernel)]; exact hprecision) rfl rfl
      simpa only [wordToElem, normalizeInt_uint256_word, hs.storageRead] using hh
    rcases vaultTotalAssetsRoutine hs hstack (by native_decide) rd6772 with
      ⟨evm', σ', calleeLocals, a, b, c, aw', out, k', C', hcallee, hs', rd1597⟩ | ⟨hcallee, hrev⟩
    swap
    · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
      apply ExecBlock.consNormal (ExecStmt.letDecl hsEval)
      apply ExecBlock.consRevert (ExecStmt.iteFalse hfalse ?_)
      exact ExecBlock.consNormal (ExecStmt.letDecl hpEval) (ExecBlock.consRevert
        (internalCallFunctionRevert (callee := vaultTotalAssetsFunction) (argVals := [])
          (by simp [evalExprs?, pure]) rfl rfl hcallee))
    let total := UInt256.sub (a + b) c
    let locals3 := locals2.insert "__c0" (.int (Int.ofNat total.toNat))
    let scratch := vaultTotalAssetsScratch mem2 a b c
    let mem3 := total.toByteArray.write 0 scratch 448 32
    have hframe := vaultTotalAssetsScratch_frame mem2 a b c (by omega)
    have hscratch : scratch.size = mem2.size := hframe.1
    have hsize3 : 480 ≤ mem3.size := toByteArray_write_size_ge_off_add32 _ _ 448 (hgap _ (by omega) _)
    have hsupply3 : memLoad (UInt256.ofNat 352) mem3 = supply := by
      rw [memLoad_below_write _ _ 448 352 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel),
        hframe.2 352 (by omega) (by omega) (by decide +kernel),
        memLoad_below_write _ _ 384 352 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel), hmSupply]
    have hprecision3 : memLoad (UInt256.ofNat 384) mem3 = precision := by
      rw [memLoad_below_write _ _ 448 384 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel),
        hframe.2 384 (by omega) (by omega) (by decide +kernel)]
      exact memLoad_write_back _ _ 384 (by decide +kernel) (hgap _ (by omega) _)
    have htotal3 : memLoad (UInt256.ofNat 448) mem3 = total := memLoad_write_back _ _ 448 (by decide +kernel) (hgap _ (by omega) _)
    have hflag3 : memLoad (UInt256.ofNat 320) mem3 = if isFloor then ⟨1⟩ else ⟨0⟩ := by
      rw [memLoad_below_write _ _ 448 320 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel),
        hframe.2 320 (by omega) (by omega) (by decide +kernel),
        memLoad_below_write _ _ 384 320 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel),
        memLoad_below_write _ _ 352 320 hsize (by omega) (hgap _ (by omega) _) (by decide +kernel), hmflag]
    have hcall := internalCallFunctionReturn (caller := {contract := contract, locals := locals2})
      (callee := vaultTotalAssetsFunction) (name := "_total_assets") (args := []) (argVals := []) (retVar := "__c0")
      (by simp [evalExprs?, pure]) rfl rfl hcallee
    have hprefix : ExecBlock fork config {contract := contract, locals := locals1} evm
        (vaultPriceNonzeroBody.take 2) (.ok {contract := contract, locals := locals3} evm') :=
      ExecBlock.consNormal (ExecStmt.letDecl hpEval) (ExecBlock.consNormal hcall ExecBlock.nil)
    have hbranch : vaultPriceNonzeroBody = vaultPriceNonzeroBody.take 2 ++
        (vaultPriceArithmeticBody ++ vaultPriceFinishBody) := rfl
    rcases vaultPriceArithmetic (evm := evm') (locals := locals3) hsize3
      (by simp only [locals3, locals2, locals1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
      (by simp only [locals3, locals2, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
      (by simp [locals3]) hsupply3 hprecision3 htotal3 (by omega) rd1597 with
      ⟨aw1, k1, C1, harith, hden, rd1689⟩ | ⟨harith, hrev⟩
    swap
    · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
      apply ExecBlock.consNormal (ExecStmt.letDecl hsEval)
      apply ExecBlock.consRevert (ExecStmt.iteFalse hfalse ?_)
      change ExecBlock fork _ _ _ vaultPriceNonzeroBody _
      rw [hbranch]
      exact execBlock_append hprefix (execBlock_reverted_append harith)
    let num := UInt256.mul vaultPriceScale (UInt256.mul total precision + ⟨1⟩)
    let den := supply + UInt256.ofNat 1000
    let locals4 := vaultPriceArithmeticLocals locals3 num den
    let mem4 := num.toByteArray.write 0 mem3 416 32
    have hsize4 : 448 ≤ mem4.size := toByteArray_write_size_ge_off_add32 _ _ 416 (hgap _ (by omega) _)
    have hnum4 : memLoad (UInt256.ofNat 416) mem4 = num := memLoad_write_back _ _ 416 (by decide +kernel) (hgap _ (by omega) _)
    have hflag4 : memLoad (UInt256.ofNat 320) mem4 = if isFloor then ⟨1⟩ else ⟨0⟩ := by
      rw [memLoad_below_write _ _ 416 320 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel), hflag3]
    have hnumLocal : locals4.get? "numerator" = some (.int (Int.ofNat num.toNat)) := by
      simp only [locals4, vaultPriceArithmeticLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl
    have hdenLocal : locals4.get? "denominator" = some (.int (Int.ofNat den.toNat)) := by
      exact store_get_self _ _ _
    have hflagLocal : locals4.get? "_is_floor" = some (.bool isFloor) := by
      change (((((locals.insert "supply" (.int (Int.ofNat supply.toNat))).insert
        "precision_" (.int (Int.ofNat precision.toNat))).insert "__c0" (.int (Int.ofNat total.toNat))).insert
        "numerator" (.int (Int.ofNat num.toNat))).insert "denominator" (.int (Int.ofNat den.toNat))).get? "_is_floor" = _
      rw [store_get_ne _ _ (by decide +kernel), store_get_ne _ _ (by decide +kernel),
        store_get_ne _ _ (by decide +kernel), store_get_ne _ _ (by decide +kernel), store_get_ne _ _ (by decide +kernel)]
      exact hflag
    rcases vaultPriceFinish hsize4 hnum4 hflag4 hden (by omega) rd1689 with ⟨hzero, hrev⟩ | ⟨hnonzero, hret⟩
    · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
      apply ExecBlock.consNormal (ExecStmt.letDecl hsEval)
      apply ExecBlock.consRevert (ExecStmt.iteFalse hfalse ?_)
      change ExecBlock fork _ _ _ vaultPriceNonzeroBody _
      rw [hbranch]
      exact execBlock_append hprefix (execBlock_append harith
        (vaultPriceFinishReverts hnumLocal hdenLocal hflagLocal hden hzero))
    · refine Or.inl ⟨evm', σ', vaultPriceResultLocals locals4 isFloor (vaultConversionResult isFloor num den),
        vaultConversionResult isFloor num den, ?_, hs', hret⟩
      apply ExecFuncBody.execBlockRet
      apply ExecBlock.consNormal (ExecStmt.letDecl hsEval)
      apply ExecBlock.consReturn (ExecStmt.iteFalse hfalse ?_)
      change ExecBlock fork _ _ _ vaultPriceNonzeroBody _
      rw [hbranch]
      exact execBlock_append hprefix (execBlock_append harith
        (vaultPriceFinishReturns hnumLocal hdenLocal hflagLocal hden hnonzero))
end Benchmarks.CurveVault

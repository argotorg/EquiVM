import Benchmarks.CurveVault.ConversionPrepare

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

abbrev vaultConvertSharesFunction : FunctionDecl := contract.functions[28]!
abbrev vaultSharesArithmeticBody : List Stmt := (vaultConvertSharesFunction.body.drop 2).take 3

def vaultSharesArithmeticLocals (locals : Store) (precision numerator denominator : UInt256) : Store :=
  ((locals.insert "precision_" (.int (Int.ofNat precision.toNat))).insert
    "numerator" (.int (Int.ofNat numerator.toNat))).insert "denominator" (.int (Int.ofNat denominator.toNat))

theorem vaultSharesArithmetic {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {assets total : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 448 ≤ mem.size)
    (hp : locals.get? "precision" = none) (hsupply : locals.get? "totalSupply" = none)
    (ha : locals.get? "_assets" = some (.int (Int.ofNat assets.toNat)))
    (ht : locals.get? "total_assets" = some (.int (Int.ofNat total.toNat)))
    (hma : memLoad (UInt256.ofNat 320) mem = assets) (hmt : memLoad (UInt256.ofNat 416) mem = total)
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 7145) R mem aw rdata σ k C) :
    let precision := codeOwnerStorageWord I σ ⟨15⟩
    let supply := codeOwnerStorageWord I σ ⟨14⟩
    let numerator := UInt256.mul (UInt256.mul (supply + UInt256.ofNat 1000) assets) precision
    let prod := UInt256.mul total precision
    (∃ aw' k' C',
      ExecBlock fork config {contract := contract, locals := locals} evm vaultSharesArithmeticBody
        (.ok {contract := contract, locals := vaultSharesArithmeticLocals locals precision numerator (prod + ⟨1⟩)} evm) ∧
      prod.toNat + 1 < UInt256.size ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat 7261) ((prod + ⟨1⟩) :: prod :: R)
        (numerator.toByteArray.write 0 (precision.toByteArray.write 0 mem 448 32) 480 32) aw' rdata σ k' C') ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm vaultSharesArithmeticBody .reverted ∧
      RDrev fork vaultBytecode g s0) := by
  dsimp only
  let p := codeOwnerStorageWord I σ ⟨15⟩
  let s := codeOwnerStorageWord I σ ⟨14⟩
  let locals1 := locals.insert "precision_" (.int (Int.ofNat p.toNat))
  let mem1 := p.toByteArray.write 0 mem 448 32
  have hpEval : evalExpr? config {contract := contract, locals := locals} evm
      (.storage {base := "precision", steps := []}) = .ok (.int (Int.ofNat p.toNat)) := by
    have hh := vaultEvalScalar evm locals "precision" (.int (.uint ⟨256, by decide⟩)) ⟨15⟩ hp rfl rfl
    simpa only [wordToElem, normalizeInt_uint256_word, hs.storageRead] using hh
  have hsEval : evalExpr? config {contract := contract, locals := locals1} evm
      (.storage {base := "totalSupply", steps := []}) = .ok (.int (Int.ofNat s.toNat)) := by
    have hh := vaultEvalScalar evm locals1 "totalSupply" (.int (.uint ⟨256, by decide⟩)) ⟨14⟩
      (by rw [store_get_ne _ _ (by decide +kernel)]; exact hsupply) rfl rfl
    simpa only [wordToElem, normalizeInt_uint256_word, hs.storageRead] using hh
  have haEval : evalExpr? config {contract := contract, locals := locals1} evm (.var "_assets") =
      .ok (.int (Int.ofNat assets.toNat)) :=
    evalExpr_varUInt256 (by rw [store_get_ne _ _ (by decide +kernel)]; exact ha)
  have h1000 : evalExpr? config {contract := contract, locals := locals1} evm (.intLit 1000) =
      .ok (.int (Int.ofNat (UInt256.ofNat 1000).toNat)) := by simp [evalExpr?, pure]; rfl
  have hpLocal : evalExpr? config {contract := contract, locals := locals1} evm (.var "precision_") =
      .ok (.int (Int.ofNat p.toNat)) := evalExpr_varUInt256 (by simp [locals1])
  have hma1 : memLoad (UInt256.ofNat 320) mem1 = assets := by
    rw [memLoad_below_write _ _ 448 320 (by omega) (by omega)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 448 (by norm_num))) (by decide +kernel)]
    exact hma
  have hmp1 : memLoad (UInt256.ofNat 448) mem1 = p :=
    memLoad_write_back _ _ 448 (by decide +kernel)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 448 (by norm_num)))
  by_cases hsum : s.toNat + (UInt256.ofNat 1000).toNat < UInt256.size
  swap
  · have hover : UInt256.size ≤ s.toNat + (UInt256.ofNat 1000).toNat := by omega
    obtain ⟨_, _, rdFail⟩ := vaultBlocks.vault_block_7145_taken (by omega)
      (by change UInt256.lt (s + UInt256.ofNat 1000) s ≠ _
          rw [u256_add_overflow_lt _ _ hover]; decide +kernel) (by native_decide) h
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_7145_taken_stack, List.length_cons]; omega) rdFail
    refine Or.inr ⟨?_, hrev⟩
    apply ExecBlock.consNormal (ExecStmt.letDecl hpEval)
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert
      (evalExpr_checked_binary_left_revert .mul _ (evalExpr_checked_binary_left_revert .mul _
        (evalExpr_add256_revert hsEval h1000 hover))))
  obtain ⟨k1, C1, rd1⟩ := vaultBlocks.vault_block_7145_fallthrough (by omega)
    (by change UInt256.lt (s + UInt256.ofNat 1000) s = _
        exact ult_zero (by rw [uadd_toNat, Nat.mod_eq_of_lt hsum]; omega)) h
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 7168) ((s + UInt256.ofNat 1000) :: s :: R)
    mem1 _ rdata σ k1 C1 at rd1
  have hsumEval := evalExpr_add256_ok hsEval h1000 rfl hsum
  by_cases hmulA : (s + UInt256.ofNat 1000).toNat * assets.toNat < UInt256.size
  swap
  · have hover : UInt256.size ≤ (s + UInt256.ofNat 1000).toNat * assets.toNat := by omega
    have rdFail := vaultBlocks.vault_block_7168_taken (by omega)
      (by rw [hma1]; exact mulCheck_overflow _ _ hover) (by native_decide) rd1
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_7168_taken_stack, List.length_cons]; omega) rdFail
    refine Or.inr ⟨?_, hrev⟩
    apply ExecBlock.consNormal (ExecStmt.letDecl hpEval)
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert
      (evalExpr_checked_binary_left_revert .mul _ (evalExpr_mul256_revert hsumEval haEval hover)))
  have rd2 := vaultBlocks.vault_block_7168_fallthrough (by omega)
    (by rw [hma1]; exact mulCheck_ok _ _ hmulA) rd1
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 7190)
    (UInt256.mul (s + UInt256.ofNat 1000) (memLoad (UInt256.ofNat 320) mem1) ::
      memLoad (UInt256.ofNat 320) mem1 :: (s + UInt256.ofNat 1000) :: R) mem1 _ rdata σ _ _ at rd2
  rw [hma1] at rd2
  have hmulAEval := evalExpr_mul256_ok hsumEval haEval rfl hmulA
  by_cases hmulP : (UInt256.mul (s + UInt256.ofNat 1000) assets).toNat * p.toNat < UInt256.size
  swap
  · have hover : UInt256.size ≤ (UInt256.mul (s + UInt256.ofNat 1000) assets).toNat * p.toNat := by omega
    have rdFail := vaultBlocks.vault_block_7190_taken (by omega)
      (by rw [hmp1]; exact mulCheck_overflow _ _ hover) (by native_decide) rd2
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_7190_taken_stack, List.length_cons]; omega) rdFail
    refine Or.inr ⟨?_, hrev⟩
    apply ExecBlock.consNormal (ExecStmt.letDecl hpEval)
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert (evalExpr_mul256_revert hmulAEval hpLocal hover))
  have rd3 := vaultBlocks.vault_block_7190_fallthrough (by omega)
    (by rw [hmp1]; exact mulCheck_ok _ _ hmulP) rd2
  let num := UInt256.mul (UInt256.mul (s + UInt256.ofNat 1000) assets) p
  let locals2 := locals1.insert "numerator" (.int (Int.ofNat num.toNat))
  let mem2 := num.toByteArray.write 0 mem1 480 32
  have hnumEval := evalExpr_mul256_ok hmulAEval hpLocal rfl hmulP
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 7214)
    (UInt256.mul (UInt256.mul (s + UInt256.ofNat 1000) assets) (memLoad (UInt256.ofNat 448) mem1) ::
      memLoad (UInt256.ofNat 448) mem1 :: UInt256.mul (s + UInt256.ofNat 1000) assets :: R)
    mem1 _ rdata σ _ _ at rd3
  rw [hmp1] at rd3
  have hm1Size : 480 ≤ mem1.size := toByteArray_write_size_ge_off_add32 _ _ 448
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 448 (by norm_num)))
  have hmt1 : memLoad (UInt256.ofNat 416) mem1 = total := by
    rw [memLoad_below_write _ _ 448 416 (by omega) (by omega)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 448 (by norm_num))) (by decide +kernel)]
    exact hmt
  have hmt2 : memLoad (UInt256.ofNat 416) mem2 = total := by
    rw [memLoad_below_write _ _ 480 416 (by omega) (by omega)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 480 (by norm_num))) (by decide +kernel)]
    exact hmt1
  have hmp2 : memLoad (UInt256.ofNat 448) mem2 = p := by
    rw [memLoad_below_write _ _ 480 448 (by omega) (by omega)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 480 (by norm_num))) (by decide +kernel)]
    exact hmp1
  have htEval : evalExpr? config {contract := contract, locals := locals2} evm (.var "total_assets") =
      .ok (.int (Int.ofNat total.toNat)) :=
    evalExpr_varUInt256 (by rw [store_get_ne _ _ (by decide +kernel), store_get_ne _ _ (by decide +kernel)]; exact ht)
  have hpEval2 : evalExpr? config {contract := contract, locals := locals2} evm (.var "precision_") =
      .ok (.int (Int.ofNat p.toNat)) :=
    evalExpr_varUInt256 (by rw [store_get_ne _ _ (by decide +kernel), store_get_self])
  have h1 : evalExpr? config {contract := contract, locals := locals2} evm (.intLit 1) =
      .ok (.int (Int.ofNat (UInt256.ofNat 1).toNat)) := by simp [evalExpr?, pure]; rfl
  by_cases hprod : total.toNat * p.toNat < UInt256.size
  swap
  · have hover : UInt256.size ≤ total.toNat * p.toNat := by omega
    have rdFail := vaultBlocks.vault_block_7214_taken (by omega)
      (by change UInt256.isZero (UInt256.lor (UInt256.eq
            (UInt256.div (UInt256.mul (memLoad (UInt256.ofNat 416) mem2) (memLoad (UInt256.ofNat 448) mem2))
              (memLoad (UInt256.ofNat 448) mem2)) (memLoad (UInt256.ofNat 416) mem2))
            (UInt256.isZero (memLoad (UInt256.ofNat 448) mem2))) ≠ _
          rw [hmt2, hmp2]; exact mulCheck_overflow _ _ hover) (by native_decide) rd3
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_7214_taken_stack, List.length_cons]; omega) rdFail
    refine Or.inr ⟨?_, hrev⟩
    apply ExecBlock.consNormal (ExecStmt.letDecl hpEval)
    apply ExecBlock.consNormal (ExecStmt.letDecl hnumEval)
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert
      (evalExpr_checked_binary_left_revert .add _ (evalExpr_mul256_revert htEval hpEval2 hover)))
  have rd4 := vaultBlocks.vault_block_7214_fallthrough (by omega)
    (by change UInt256.isZero (UInt256.lor (UInt256.eq
          (UInt256.div (UInt256.mul (memLoad (UInt256.ofNat 416) mem2) (memLoad (UInt256.ofNat 448) mem2))
            (memLoad (UInt256.ofNat 448) mem2)) (memLoad (UInt256.ofNat 416) mem2))
          (UInt256.isZero (memLoad (UInt256.ofNat 448) mem2))) = _
        rw [hmt2, hmp2]; exact mulCheck_ok _ _ hprod) rd3
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 7246)
    (UInt256.mul (memLoad (UInt256.ofNat 416) mem2) (memLoad (UInt256.ofNat 448) mem2) ::
      memLoad (UInt256.ofNat 448) mem2 :: memLoad (UInt256.ofNat 416) mem2 :: R) mem2 _ rdata σ _ _ at rd4
  rw [hmt2, hmp2] at rd4
  have hprodEval := evalExpr_mul256_ok htEval hpEval2 rfl hprod
  by_cases hdenom : (UInt256.mul total p).toNat + (UInt256.ofNat 1).toNat < UInt256.size
  · have rdNext := vaultBlocks.vault_block_7246_fallthrough (by omega)
      (ult_zero (by rw [uadd_toNat, Nat.mod_eq_of_lt hdenom]; omega)) rd4
    refine Or.inl ⟨_, _, _, ?_, hdenom, rdNext⟩
    apply ExecBlock.consNormal (ExecStmt.letDecl hpEval)
    apply ExecBlock.consNormal (ExecStmt.letDecl hnumEval)
    exact ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_add256_ok hprodEval h1 rfl hdenom)) ExecBlock.nil
  · have hover : UInt256.size ≤ (UInt256.mul total p).toNat + (UInt256.ofNat 1).toNat := by omega
    have rdFail := vaultBlocks.vault_block_7246_taken (by omega)
      (by rw [u256_add_overflow_lt _ _ hover]; decide +kernel) (by native_decide) rd4
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_7246_taken_stack, List.length_cons]; omega) rdFail
    refine Or.inr ⟨?_, hrev⟩
    apply ExecBlock.consNormal (ExecStmt.letDecl hpEval)
    apply ExecBlock.consNormal (ExecStmt.letDecl hnumEval)
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert (evalExpr_add256_revert hprodEval h1 hover))
end Benchmarks.CurveVault

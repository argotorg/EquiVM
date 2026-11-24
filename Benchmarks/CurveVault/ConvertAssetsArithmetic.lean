import Benchmarks.CurveVault.ConvertSharesArithmetic

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

abbrev vaultConvertAssetsFunction : FunctionDecl := contract.functions[29]!
abbrev vaultAssetsArithmeticBody : List Stmt := (vaultConvertAssetsFunction.body.drop 2).take 3

theorem vaultAssetsArithmetic {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {shares total : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 448 ≤ mem.size)
    (hp : locals.get? "precision" = none) (hsupply : locals.get? "totalSupply" = none)
    (ha : locals.get? "_shares" = some (.int (Int.ofNat shares.toNat)))
    (ht : locals.get? "total_assets" = some (.int (Int.ofNat total.toNat)))
    (hma : memLoad (UInt256.ofNat 320) mem = shares) (hmt : memLoad (UInt256.ofNat 416) mem = total)
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 7369) R mem aw rdata σ k C) :
    let precision := codeOwnerStorageWord I σ ⟨15⟩
    let supply := codeOwnerStorageWord I σ ⟨14⟩
    let numerator := UInt256.mul shares (UInt256.mul total precision + ⟨1⟩)
    let denominator := UInt256.mul (supply + UInt256.ofNat 1000) precision
    (∃ aw' k' C',
      ExecBlock fork config {contract := contract, locals := locals} evm vaultAssetsArithmeticBody
        (.ok {contract := contract, locals := vaultSharesArithmeticLocals locals precision numerator denominator} evm) ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat 7483) (denominator :: precision :: (supply + UInt256.ofNat 1000) :: R)
        (numerator.toByteArray.write 0 (precision.toByteArray.write 0 mem 448 32) 480 32) aw' rdata σ k' C') ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm vaultAssetsArithmeticBody .reverted ∧
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
  have haEval : evalExpr? config {contract := contract, locals := locals1} evm (.var "_shares") =
      .ok (.int (Int.ofNat shares.toNat)) :=
    evalExpr_varUInt256 (by rw [store_get_ne _ _ (by decide +kernel)]; exact ha)
  have htEval : evalExpr? config {contract := contract, locals := locals1} evm (.var "total_assets") =
      .ok (.int (Int.ofNat total.toNat)) :=
    evalExpr_varUInt256 (by rw [store_get_ne _ _ (by decide +kernel)]; exact ht)
  have hpLocal : evalExpr? config {contract := contract, locals := locals1} evm (.var "precision_") =
      .ok (.int (Int.ofNat p.toNat)) := evalExpr_varUInt256 (by simp [locals1])
  have h1 : evalExpr? config {contract := contract, locals := locals1} evm (.intLit 1) =
      .ok (.int (Int.ofNat (UInt256.ofNat 1).toNat)) := by simp [evalExpr?, pure]; rfl
  have hgap : 448 - mem.size < USize.size := lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 448 (by norm_num))
  have hm1Size : 480 ≤ mem1.size := toByteArray_write_size_ge_off_add32 _ _ 448 hgap
  have hma1 : memLoad (UInt256.ofNat 320) mem1 = shares := by
    rw [memLoad_below_write _ _ 448 320 (by omega) (by omega) hgap (by decide +kernel), hma]
  have hmt1 : memLoad (UInt256.ofNat 416) mem1 = total := by
    rw [memLoad_below_write _ _ 448 416 (by omega) (by omega) hgap (by decide +kernel), hmt]
  have hmp1 : memLoad (UInt256.ofNat 448) mem1 = p := memLoad_write_back _ _ 448 (by decide +kernel) hgap
  have hcheck : ∀ b, UInt256.isZero (UInt256.lor (UInt256.eq
      (UInt256.div (UInt256.mul (memLoad (UInt256.ofNat 416) mem1) (memLoad (UInt256.ofNat 448) mem1))
        (memLoad (UInt256.ofNat 448) mem1)) (memLoad (UInt256.ofNat 416) mem1))
      (UInt256.isZero (memLoad (UInt256.ofNat 448) mem1))) = b ↔
      UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul total p) p) total)
        (UInt256.isZero p)) = b := by intro b; rw [hmt1, hmp1]
  by_cases hprod : total.toNat * p.toNat < UInt256.size
  swap
  · have hover : UInt256.size ≤ total.toNat * p.toNat := by omega
    obtain ⟨_, _, rdFail⟩ := vaultBlocks.vault_block_7369_taken (by omega)
      (fun hz => (mulCheck_overflow _ _ hover) ((hcheck _).mp hz)) (by native_decide) h
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_7369_taken_stack, List.length_cons]; omega) rdFail
    refine Or.inr ⟨?_, hrev⟩
    apply ExecBlock.consNormal (ExecStmt.letDecl hpEval)
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert
      (evalExpr_checked_mul_right_revert _ haEval
        (evalExpr_checked_binary_left_revert .add _ (evalExpr_mul256_revert htEval hpLocal hover))))
  obtain ⟨_, _, rd7405⟩ := vaultBlocks.vault_block_7369_fallthrough (by omega)
    ((hcheck _).mpr (mulCheck_ok _ _ hprod)) h
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 7405)
    (UInt256.mul (memLoad (UInt256.ofNat 416) mem1) (memLoad (UInt256.ofNat 448) mem1) ::
      memLoad (UInt256.ofNat 448) mem1 :: memLoad (UInt256.ofNat 416) mem1 ::
      memLoad (UInt256.ofNat 320) mem1 :: R) mem1 _ rdata σ _ _ at rd7405
  rw [hmt1, hmp1, hma1] at rd7405
  have hprodEval := evalExpr_mul256_ok htEval hpLocal rfl hprod
  by_cases hincr : (UInt256.mul total p).toNat + (UInt256.ofNat 1).toNat < UInt256.size
  swap
  · have hover : UInt256.size ≤ (UInt256.mul total p).toNat + (UInt256.ofNat 1).toNat := by omega
    have rdFail := vaultBlocks.vault_block_7405_taken (by simp only [List.length_cons]; omega)
      (by rw [u256_add_overflow_lt _ _ hover]; decide +kernel) (by native_decide) rd7405
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_7405_taken_stack, List.length_cons]; omega) rdFail
    refine Or.inr ⟨?_, hrev⟩
    apply ExecBlock.consNormal (ExecStmt.letDecl hpEval)
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert
      (evalExpr_checked_mul_right_revert _ haEval (evalExpr_add256_revert hprodEval h1 hover)))
  have rd7420 := vaultBlocks.vault_block_7405_fallthrough (by simp only [List.length_cons]; omega)
    (ult_zero (by rw [uadd_toNat, Nat.mod_eq_of_lt hincr]; omega)) rd7405
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 7420)
    ((UInt256.mul total p + UInt256.ofNat 1) :: UInt256.mul total p :: shares :: R) mem1 _ rdata σ _ _ at rd7420
  have hincrEval := evalExpr_add256_ok hprodEval h1 rfl hincr
  by_cases hnum : shares.toNat * (UInt256.mul total p + UInt256.ofNat 1).toNat < UInt256.size
  swap
  · have hover : UInt256.size ≤ shares.toNat * (UInt256.mul total p + UInt256.ofNat 1).toNat := by omega
    have rdFail := vaultBlocks.vault_block_7420_taken (by omega) (mulCheck_overflow _ _ hover) (by native_decide) rd7420
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_7420_taken_stack, List.length_cons]; omega) rdFail
    exact Or.inr ⟨ExecBlock.consNormal (ExecStmt.letDecl hpEval)
      (ExecBlock.consRevert (ExecStmt.letDeclRevert (evalExpr_mul256_revert haEval hincrEval hover))), hrev⟩
  have rd7438 := vaultBlocks.vault_block_7420_fallthrough (by omega) (mulCheck_ok _ _ hnum) rd7420
  have hnumEval := evalExpr_mul256_ok haEval hincrEval rfl hnum
  let num := UInt256.mul shares (UInt256.mul total p + UInt256.ofNat 1)
  let locals2 := locals1.insert "numerator" (.int (Int.ofNat num.toNat))
  let mem2 := num.toByteArray.write 0 mem1 480 32
  have hsEval : evalExpr? config {contract := contract, locals := locals2} evm
      (.storage {base := "totalSupply", steps := []}) = .ok (.int (Int.ofNat s.toNat)) := by
    have hh := vaultEvalScalar evm locals2 "totalSupply" (.int (.uint ⟨256, by decide⟩)) ⟨14⟩
      (by rw [store_get_ne _ _ (by decide +kernel), store_get_ne _ _ (by decide +kernel)]; exact hsupply) rfl rfl
    simpa only [wordToElem, normalizeInt_uint256_word, hs.storageRead] using hh
  have h1000 : evalExpr? config {contract := contract, locals := locals2} evm (.intLit 1000) =
      .ok (.int (Int.ofNat (UInt256.ofNat 1000).toNat)) := by simp [evalExpr?, pure]; rfl
  have hpEval2 : evalExpr? config {contract := contract, locals := locals2} evm (.var "precision_") =
      .ok (.int (Int.ofNat p.toNat)) :=
    evalExpr_varUInt256 (by rw [store_get_ne _ _ (by decide +kernel), store_get_self])
  have hmp2 : memLoad (UInt256.ofNat 448) mem2 = p := by
    rw [memLoad_below_write _ _ 480 448 (by omega) (by omega)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 480 (by norm_num))) (by decide +kernel), hmp1]
  by_cases hsum : s.toNat + (UInt256.ofNat 1000).toNat < UInt256.size
  swap
  · have hover : UInt256.size ≤ s.toNat + (UInt256.ofNat 1000).toNat := by omega
    obtain ⟨_, _, rdFail⟩ := vaultBlocks.vault_block_7438_taken (by omega)
      (by change UInt256.lt (s + UInt256.ofNat 1000) s ≠ _
          rw [u256_add_overflow_lt _ _ hover]; decide +kernel) (by native_decide) rd7438
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_7438_taken_stack, List.length_cons]; omega) rdFail
    exact Or.inr ⟨ExecBlock.consNormal (ExecStmt.letDecl hpEval)
      (ExecBlock.consNormal (ExecStmt.letDecl hnumEval) (ExecBlock.consRevert (ExecStmt.letDeclRevert
        (evalExpr_checked_binary_left_revert .mul _ (evalExpr_add256_revert hsEval h1000 hover))))), hrev⟩
  obtain ⟨_, _, rd7461⟩ := vaultBlocks.vault_block_7438_fallthrough (by omega)
    (by change UInt256.lt (s + UInt256.ofNat 1000) s = _
        exact ult_zero (by rw [uadd_toNat, Nat.mod_eq_of_lt hsum]; omega)) rd7438
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 7461) ((s + UInt256.ofNat 1000) :: s :: R) mem2 _ rdata σ _ _ at rd7461
  have hsumEval := evalExpr_add256_ok hsEval h1000 rfl hsum
  by_cases hden : (s + UInt256.ofNat 1000).toNat * p.toNat < UInt256.size
  · have rdNext := vaultBlocks.vault_block_7461_fallthrough (by omega)
      (by rw [hmp2]; exact mulCheck_ok _ _ hden) rd7461
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 7483)
      (UInt256.mul (s + UInt256.ofNat 1000) (memLoad (UInt256.ofNat 448) mem2) ::
        memLoad (UInt256.ofNat 448) mem2 :: (s + UInt256.ofNat 1000) :: R) mem2 _ rdata σ _ _ at rdNext
    rw [hmp2] at rdNext
    refine Or.inl ⟨_, _, _, ?_, rdNext⟩
    exact ExecBlock.consNormal (ExecStmt.letDecl hpEval)
      (ExecBlock.consNormal (ExecStmt.letDecl hnumEval)
        (ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_mul256_ok hsumEval hpEval2 rfl hden)) ExecBlock.nil))
  · have hover : UInt256.size ≤ (s + UInt256.ofNat 1000).toNat * p.toNat := by omega
    have rdFail := vaultBlocks.vault_block_7461_taken (by omega)
      (by rw [hmp2]; exact mulCheck_overflow _ _ hover) (by native_decide) rd7461
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_7461_taken_stack, List.length_cons]; omega) rdFail
    exact Or.inr ⟨ExecBlock.consNormal (ExecStmt.letDecl hpEval)
      (ExecBlock.consNormal (ExecStmt.letDecl hnumEval)
        (ExecBlock.consRevert (ExecStmt.letDeclRevert (evalExpr_mul256_revert hsumEval hpEval2 hover)))), hrev⟩
end Benchmarks.CurveVault

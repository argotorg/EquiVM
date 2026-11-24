import Benchmarks.CurveVault.ConvertAssetsArithmetic
import Benchmarks.CurveVault.RuntimeBlocks_008

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

abbrev vaultPriceFunction : FunctionDecl := contract.functions[5]!
abbrev vaultPriceNonzeroBody : List Stmt := match vaultPriceFunction.body[1]! with
  | .ite _ _ body => body
  | _ => []
abbrev vaultPriceArithmeticBody : List Stmt := (vaultPriceNonzeroBody.drop 2).take 2
abbrev vaultPriceScale : UInt256 := UInt256.ofNat 1000000000000000000
abbrev vaultPriceScaleExpr : Expr := .inRange (.uint ⟨256, by decide⟩)
  (.binary .exp (.intLit 10) (.intLit 18))

theorem vaultPriceScaleEval (evm : State) (locals : Store) :
    evalExpr? config {contract := contract, locals := locals} evm vaultPriceScaleExpr =
      .ok (.int (Int.ofNat vaultPriceScale.toNat)) := by
  simp only [vaultPriceScaleExpr, evalExpr?, evalBinaryOp?, bind, pure, EvalResult.bind]
  rfl

def vaultPriceArithmeticLocals (locals : Store) (num den : UInt256) : Store :=
  (locals.insert "numerator" (.int (Int.ofNat num.toNat))).insert "denominator" (.int (Int.ofNat den.toNat))

theorem vaultPriceArithmetic {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {supply precision total : UInt256} {R : List UInt256} {locals : Store}
    (hsize : 480 ≤ mem.size)
    (hs : locals.get? "supply" = some (.int (Int.ofNat supply.toNat)))
    (hp : locals.get? "precision_" = some (.int (Int.ofNat precision.toNat)))
    (ht : locals.get? "__c0" = some (.int (Int.ofNat total.toNat)))
    (hms : memLoad (UInt256.ofNat 352) mem = supply)
    (hmp : memLoad (UInt256.ofNat 384) mem = precision)
    (hmt : memLoad (UInt256.ofNat 448) mem = total)
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 1597) R mem aw rdata σ k C) :
    let numerator := UInt256.mul vaultPriceScale (UInt256.mul total precision + ⟨1⟩)
    let denominator := supply + UInt256.ofNat 1000
    (∃ aw' k' C',
      ExecBlock fork config {contract := contract, locals := locals} evm vaultPriceArithmeticBody
        (.ok {contract := contract, locals := vaultPriceArithmeticLocals locals numerator denominator} evm) ∧
      denominator ≠ ⟨0⟩ ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat 1689) (denominator :: supply :: R)
        (numerator.toByteArray.write 0 mem 416 32) aw' rdata σ k' C') ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm vaultPriceArithmeticBody .reverted ∧
      RDrev fork vaultBytecode g s0) := by
  dsimp only
  have htEval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) ht
  have hpEval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) hp
  have hscale := vaultPriceScaleEval evm locals
  have h1 : evalExpr? config {contract := contract, locals := locals} evm (.intLit 1) =
      .ok (.int (Int.ofNat (UInt256.ofNat 1).toNat)) := by simp [evalExpr?, pure]; rfl
  by_cases hprod : total.toNat * precision.toNat < UInt256.size
  swap
  · have hover : UInt256.size ≤ total.toNat * precision.toNat := by omega
    have rdFail := vaultBlocks.vault_block_1597_taken hstack
      (by rw [hmt, hmp]; exact mulCheck_overflow _ _ hover) (by native_decide) h
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_1597_taken_stack, List.length_cons]; omega) rdFail
    exact Or.inr ⟨ExecBlock.consRevert (ExecStmt.letDeclRevert
      (evalExpr_checked_mul_right_revert _ hscale
        (evalExpr_checked_binary_left_revert .add _ (evalExpr_mul256_revert htEval hpEval hover)))), hrev⟩
  have rd1622 := vaultBlocks.vault_block_1597_fallthrough hstack
    (by rw [hmt, hmp]; exact mulCheck_ok _ _ hprod) h
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 1622)
    (UInt256.mul (memLoad (UInt256.ofNat 448) mem) (memLoad (UInt256.ofNat 384) mem) ::
      memLoad (UInt256.ofNat 384) mem :: memLoad (UInt256.ofNat 448) mem :: R) mem _ rdata σ _ _ at rd1622
  rw [hmt, hmp] at rd1622
  have hprodEval := evalExpr_mul256_ok htEval hpEval rfl hprod
  by_cases hincr : (UInt256.mul total precision).toNat + (UInt256.ofNat 1).toNat < UInt256.size
  swap
  · have hover : UInt256.size ≤ (UInt256.mul total precision).toNat + (UInt256.ofNat 1).toNat := by omega
    have rdFail := vaultBlocks.vault_block_1622_taken (by omega)
      (by rw [u256_add_overflow_lt _ _ hover]; decide +kernel) (by native_decide) rd1622
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_1622_taken_stack, List.length_cons]; omega) rdFail
    exact Or.inr ⟨ExecBlock.consRevert (ExecStmt.letDeclRevert
      (evalExpr_checked_mul_right_revert _ hscale (evalExpr_add256_revert hprodEval h1 hover))), hrev⟩
  have rd1637 := vaultBlocks.vault_block_1622_fallthrough (by omega)
    (ult_zero (by rw [uadd_toNat, Nat.mod_eq_of_lt hincr]; omega)) rd1622
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 1637)
    ((UInt256.mul total precision + UInt256.ofNat 1) :: UInt256.mul total precision :: R) mem _ rdata σ _ _ at rd1637
  have hincrEval := evalExpr_add256_ok hprodEval h1 rfl hincr
  by_cases hnum : vaultPriceScale.toNat * (UInt256.mul total precision + UInt256.ofNat 1).toNat < UInt256.size
  swap
  · have hover : UInt256.size ≤ vaultPriceScale.toNat * (UInt256.mul total precision + UInt256.ofNat 1).toNat := by omega
    have rdFail := vaultBlocks.vault_block_1637_taken (by omega)
      (u256_xor_ne_zero_of_ne (u256_mul_div_right_overflow_ne _ _ (by simpa only [Nat.mul_comm] using hover)))
      (by native_decide) rd1637
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_1637_taken_stack, List.length_cons]; omega) rdFail
    exact Or.inr ⟨ExecBlock.consRevert (ExecStmt.letDeclRevert (evalExpr_mul256_revert hscale hincrEval hover)), hrev⟩
  have rd1667 := vaultBlocks.vault_block_1637_fallthrough (by omega)
    (by rw [u256_mul_div_right_eq_of_noOverflow _ _ (by decide +kernel)
      (by simpa only [Nat.mul_comm] using hnum), u256_xor_self]; rfl) rd1637
  let num := UInt256.mul vaultPriceScale (UInt256.mul total precision + UInt256.ofNat 1)
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 1667)
    (UInt256.mul (UInt256.mul total precision + UInt256.ofNat 1) vaultPriceScale ::
      (UInt256.mul total precision + UInt256.ofNat 1) :: R) mem _ rdata σ _ _ at rd1667
  rw [u256_mul_comm (UInt256.mul total precision + UInt256.ofNat 1) vaultPriceScale] at rd1667
  have hnumEval := evalExpr_mul256_ok hscale hincrEval rfl hnum
  let locals1 := locals.insert "numerator" (.int (Int.ofNat num.toNat))
  let mem1 := num.toByteArray.write 0 mem 416 32
  have hsEval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm)
    (show locals1.get? "supply" = some (.int (Int.ofNat supply.toNat)) by
      rw [store_get_ne _ _ (by decide +kernel)]; exact hs)
  have h1000 : evalExpr? config {contract := contract, locals := locals1} evm (.intLit 1000) =
      .ok (.int (Int.ofNat (UInt256.ofNat 1000).toNat)) := by simp [evalExpr?, pure]; rfl
  have hms1 : memLoad (UInt256.ofNat 352) mem1 = supply := by
    rw [memLoad_below_write _ _ 416 352 (by omega) (by omega)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 416 (by norm_num))) (by decide +kernel), hms]
  by_cases hsum : supply.toNat + (UInt256.ofNat 1000).toNat < UInt256.size
  · have rdNext := vaultBlocks.vault_block_1667_fallthrough (by omega)
      (by change UInt256.lt (memLoad (UInt256.ofNat 352) mem1 + UInt256.ofNat 1000) (memLoad (UInt256.ofNat 352) mem1) = _
          rw [hms1]; exact ult_zero (by rw [uadd_toNat, Nat.mod_eq_of_lt hsum]; omega)) rd1667
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 1689)
      ((memLoad (UInt256.ofNat 352) mem1 + UInt256.ofNat 1000) :: memLoad (UInt256.ofNat 352) mem1 :: R)
      mem1 _ rdata σ _ _ at rdNext
    rw [hms1] at rdNext
    refine Or.inl ⟨_, _, _, ?_, ?_, rdNext⟩
    · exact ExecBlock.consNormal (ExecStmt.letDecl hnumEval)
        (ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_add256_ok hsEval h1000 rfl hsum)) ExecBlock.nil)
    · intro hz
      have hn := congrArg UInt256.toNat hz
      rw [uadd_toNat, Nat.mod_eq_of_lt hsum] at hn
      change supply.toNat + 1000 = 0 at hn
      omega
  · have hover : UInt256.size ≤ supply.toNat + (UInt256.ofNat 1000).toNat := by omega
    have rdFail := vaultBlocks.vault_block_1667_taken (by omega)
      (by change UInt256.lt (memLoad (UInt256.ofNat 352) mem1 + UInt256.ofNat 1000) (memLoad (UInt256.ofNat 352) mem1) ≠ _
          rw [hms1, u256_add_overflow_lt _ _ hover]; decide +kernel) (by native_decide) rd1667
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_1667_taken_stack, List.length_cons]; omega) rdFail
    exact Or.inr ⟨ExecBlock.consNormal (ExecStmt.letDecl hnumEval)
      (ExecBlock.consRevert (ExecStmt.letDeclRevert (evalExpr_add256_revert hsEval h1000 hover))), hrev⟩
end Benchmarks.CurveVault

import Benchmarks.UniswapV4PoolManager.Values

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev poolTicksFunction : FunctionDecl := contract.functions[60]!
theorem poolTicks_lookup : lookupCallable? contract "Pool_checkTicks" = some poolTicksFunction.toCallable := rfl

def poolTicksValid (lower upper : UInt256) : Prop :=
  EVM.signed lower < EVM.signed upper ∧ -887272 ≤ EVM.signed lower ∧ EVM.signed upper ≤ 887272
instance (lower upper : UInt256) : Decidable (poolTicksValid lower upper) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem poolTicksBody {f : Frame} {evm : EVM.State} {lower upper : UInt256}
    (hl : f.locals.get? "tickLower" = some (.int (EVM.signed lower)))
    (hu : f.locals.get? "tickUpper" = some (.int (EVM.signed upper))) :
    ExecFuncBody config f evm poolTicksFunction.body
      (if poolTicksValid lower upper then .returned f evm none else .reverted) := by
  have he0 : evalExpr? config f evm (.binary .ge (.var "tickLower") (.var "tickUpper")) =
      .ok (.bool (decide (EVM.signed upper ≤ EVM.signed lower))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hl, evalLocalValue hu]
    rfl
  have he1 : evalExpr? config f evm (.binary .lt (.var "tickLower") (.unary .neg (.intLit 887272))) =
      .ok (.bool (decide (EVM.signed lower < -887272))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hl]
    simp only [evalExpr?, bind, EvalResult.bind, pure, evalUnaryOp?, EvalResult.ofOption, evalBinaryOp?]
  have he2 : evalExpr? config f evm (.binary .gt (.var "tickUpper") (.intLit 887272)) =
      .ok (.bool (decide (887272 < EVM.signed upper))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hu]
    simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?]
  by_cases h0 : EVM.signed lower < EVM.signed upper
  · rw [decide_eq_false (by omega : ¬EVM.signed upper ≤ EVM.signed lower)] at he0
    have hs0 := ExecStmt.iteFalse (thenB := [.require (.boolLit false)]) he0 ExecBlock.nil
    by_cases h1 : -887272 ≤ EVM.signed lower
    · rw [decide_eq_false (by omega : ¬EVM.signed lower < -887272)] at he1
      have hs1 := ExecStmt.iteFalse (thenB := [.require (.boolLit false)]) he1 ExecBlock.nil
      by_cases h2 : EVM.signed upper ≤ 887272
      · rw [if_pos ⟨h0, h1, h2⟩]
        rw [decide_eq_false (by omega : ¬887272 < EVM.signed upper)] at he2
        exact .execBlockOK (ExecBlock.consNormal hs0 (ExecBlock.consNormal hs1
          (execBlock_singleton (ExecStmt.iteFalse he2 ExecBlock.nil))))
      · rw [if_neg (fun hh => h2 hh.2.2)]
        rw [decide_eq_true (by omega : 887272 < EVM.signed upper)] at he2
        exact .execBlockRevert (ExecBlock.consNormal hs0 (ExecBlock.consNormal hs1
          (ExecBlock.consRevert (ExecStmt.iteTrue he2 (ExecBlock.consRevert
            (ExecStmt.requireFalse (by simp only [evalExpr?, pure])))))))
    · rw [if_neg (fun hh => h1 hh.2.1)]
      rw [decide_eq_true (by omega : EVM.signed lower < -887272)] at he1
      exact .execBlockRevert (ExecBlock.consNormal hs0 (ExecBlock.consRevert
        (ExecStmt.iteTrue he1 (ExecBlock.consRevert (ExecStmt.requireFalse
          (by simp only [evalExpr?, pure]))))))
  · rw [if_neg (fun hh => h0 hh.1)]
    rw [decide_eq_true (by omega : EVM.signed upper ≤ EVM.signed lower)] at he0
    exact .execBlockRevert (ExecBlock.consRevert (ExecStmt.iteTrue he0
      (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure])))))

theorem poolTicksCall {f : Frame} {evm : EVM.State} {el eu : Expr} {lower upper : UInt256}
    (hf : f.contract = contract) (hl : evalExpr? config f evm el = .ok (.int (EVM.signed lower)))
    (hu : evalExpr? config f evm eu = .ok (.int (EVM.signed upper))) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "Pool_checkTicks" [el, eu] retVar)
      (if poolTicksValid lower upper then .ok {f with locals := f.locals.insert retVar .unit} evm else .reverted) := by
  have hb := poolTicksBody (f := {f with locals := (((∅ : Store).insert "tickUpper"
    (.int (EVM.signed upper))).insert "tickLower" (.int (EVM.signed lower)))}) (evm := evm)
    (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("tickLower" == "tickUpper") = false)).trans (store_get_self _ _ _))
  have hargs : evalExprs? config f evm [el, eu] = .ok [.int (EVM.signed lower), .int (EVM.signed upper)] := by
    simp only [evalExprs?, hl, hu, bind, EvalResult.bind, pure]
  have hlookup : lookupCallable? f.contract "Pool_checkTicks" = some poolTicksFunction.toCallable := by
    rw [hf]; exact poolTicks_lookup
  by_cases hvalid : poolTicksValid lower upper
  · rw [if_pos hvalid] at hb ⊢
    exact internalCallFunctionReturn hargs hlookup rfl hb
  · rw [if_neg hvalid] at hb ⊢
    exact internalCallFunctionRevert hargs hlookup rfl hb

end Benchmarks.UniswapV4PoolManager

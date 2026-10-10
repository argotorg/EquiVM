import Benchmarks.UniswapV4PoolManager.SignedNormalizeRange
import Benchmarks.UniswapV4PoolManager.WordLocals
import Benchmarks.UniswapV4PoolManager.PoolCheckSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev signedToInt128Function : FunctionDecl := contract.functions[18]!
theorem signedToInt128_lookup : lookupCallable? contract "SafeCast_toInt128" =
    some signedToInt128Function.toCallable := rfl

theorem signedToInt128Body {f : Frame} {evm : EVM.State} {n : Int}
    (hx : f.locals.get? "x" = some (.int n)) :
    ∃ f', ExecFuncBody config f evm signedToInt128Function.body
      (if signedFits ⟨128, by decide⟩ n then .returned f' evm (some [.int n]) else .reverted) := by
  let f0 := wordLocal f "y" ⟨0⟩
  let f1 := {f0 with locals := f0.locals.insert "y" (.int (normalizeInt (.sint ⟨128, by decide⟩) n))}
  have h0 : ExecStmt config f evm signedToInt128Function.body[0]! (.ok f0 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have hx0 : f0.locals.get? "x" = some (.int n) := by
    simp only [f0, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hx]
  have h1 : ExecStmt config f0 evm signedToInt128Function.body[1]! (.ok f1 evm) :=
    ExecStmt.assign (evalExpr_cast_int (intType := .sint ⟨128, by decide⟩) (evalLocalValue hx0))
      (assignLocalValue (store_get_self _ _ _))
  have hx1 : f1.locals.get? "x" = some (.int n) :=
    (store_get_ne _ _ (by decide : ("y" == "x") = false)).trans hx0
  have hy : f1.locals.get? "y" = some (.int (normalizeInt (.sint ⟨128, by decide⟩) n)) := store_get_self _ _ _
  have hguard : evalExpr? config f1 evm (.binary .ne (.var "y") (.var "x")) =
      .ok (.bool (decide (¬signedFits ⟨128, by decide⟩ n))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hy, evalLocalValue hx1]
    simp only [bind, EvalResult.bind, evalBinaryOp?, BEq.beq, Value.int.injEq,
      normalizeSigned_eq_self_iff, decide_not]
  by_cases hfit : signedFits ⟨128, by decide⟩ n
  · simp only [if_pos hfit]
    have hy' : f1.locals.get? "y" = some (.int n) := by
      simpa only [normalizeSigned_of_fits hfit] using hy
    exact ⟨f1, ExecFuncBody.execBlockRet (ExecBlock.consNormal h0 (ExecBlock.consNormal h1
      (ExecBlock.consNormal (ExecStmt.iteFalse
        (by simpa only [decide_eq_false (not_not_intro hfit)] using hguard) ExecBlock.nil)
        (ABlock.start.returns (evalLocalValue hy')))))⟩
  · simp only [if_neg hfit]
    exact ⟨f1, ExecFuncBody.execBlockRevert (ExecBlock.consNormal h0 (ExecBlock.consNormal h1
      (ExecBlock.consRevert (ExecStmt.iteTrue (by simpa only [decide_eq_true hfit] using hguard)
        (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure])))))))⟩

theorem signedToInt128Call {f : Frame} {evm : EVM.State} {n : Int} {e : Expr}
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (.int n)) (ret : Ident) :
    ExecStmt config f evm (.internalCall "SafeCast_toInt128" [e] ret)
      (if signedFits ⟨128, by decide⟩ n then .ok {f with locals := f.locals.insert ret (.int n)} evm
       else .reverted) := by
  let fc : Frame := {f with locals := (∅ : Store).insert "x" (.int n)}
  obtain ⟨f', hbody⟩ := signedToInt128Body (f := fc) (evm := evm) (store_get_self _ _ _)
  have hlookup : lookupCallable? f.contract "SafeCast_toInt128" = some signedToInt128Function.toCallable := by
    rw [hf]; exact signedToInt128_lookup
  by_cases hfit : signedFits ⟨128, by decide⟩ n
  · rw [if_pos hfit] at hbody ⊢
    exact internalCallFunctionReturn (evalExprs?_singleton he) hlookup rfl hbody
  · rw [if_neg hfit] at hbody ⊢
    exact internalCallFunctionRevert (evalExprs?_singleton he) hlookup rfl hbody

end Benchmarks.UniswapV4PoolManager

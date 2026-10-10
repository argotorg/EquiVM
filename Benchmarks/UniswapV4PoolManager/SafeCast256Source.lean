import Benchmarks.UniswapV4PoolManager.WordSignedRepresentation
import Benchmarks.UniswapV4PoolManager.WordLocals
import Benchmarks.UniswapV4PoolManager.PoolCheckSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev uintToInt256Function : FunctionDecl := contract.functions[92]!
theorem uintToInt256_lookup : lookupCallable? contract "SafeCast_toInt256" =
    some uintToInt256Function.toCallable := rfl

-- LIBRARY CANDIDATE: a word's signed interpretation is negative exactly when its high bit is set.
theorem signedNegative_iff (w : UInt256) : EVM.signed w < 0 ↔ ¬w.toNat < 2^255 := by
  have hb := w.val.isLt
  change w.toNat < 2^256 at hb
  change (if w.toNat < 2^255 then (w.toNat : Int) else w.toNat - 2^256) < 0 ↔ _
  split_ifs <;> omega

theorem uintToInt256Body {f : Frame} {evm : EVM.State} {w : UInt256}
    (hx : f.locals.get? "x" = some (.int (Int.ofNat w.toNat))) :
    ∃ f', ExecFuncBody config f evm uintToInt256Function.body
      (if w.toNat < 2^255 then .returned f' evm (some [.int (EVM.signed w)]) else .reverted) := by
  let f0 := wordLocal f "y" ⟨0⟩
  let f1 := {f0 with locals := f0.locals.insert "y" (.int (EVM.signed w))}
  have h0 : ExecStmt config f evm uintToInt256Function.body[0]! (.ok f0 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have hx0 : f0.locals.get? "x" = some (.int (Int.ofNat w.toNat)) := by
    simp only [f0, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hx]
  have hcast := evalExpr_cast_int (intType := .sint ⟨256, by decide⟩)
    (evalLocalValue (cfg := config) (f := f0) (evm := evm) hx0)
  rw [normalizeInt_sint256_word] at hcast
  have h1 : ExecStmt config f0 evm uintToInt256Function.body[1]! (.ok f1 evm) :=
    ExecStmt.assign hcast (assignLocalValue (store_get_self _ _ _))
  have hy : f1.locals.get? "y" = some (.int (EVM.signed w)) := store_get_self _ _ _
  have hguard : evalExpr? config f1 evm (.binary .lt (.var "y") (.intLit 0)) =
      .ok (.bool (decide (EVM.signed w < 0))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hy]
    simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?]
  by_cases hfit : w.toNat < 2^255
  · simp only [if_pos hfit]
    have hn : ¬EVM.signed w < 0 := fun h => (signedNegative_iff w).mp h hfit
    exact ⟨f1, ExecFuncBody.execBlockRet (ExecBlock.consNormal h0 (ExecBlock.consNormal h1
      (ExecBlock.consNormal (ExecStmt.iteFalse (by simpa only [decide_eq_false hn] using hguard) ExecBlock.nil)
        (ABlock.start.returns (evalLocalValue hy)))))⟩
  · simp only [if_neg hfit]
    have hn : EVM.signed w < 0 := (signedNegative_iff w).mpr hfit
    exact ⟨f1, ExecFuncBody.execBlockRevert (ExecBlock.consNormal h0 (ExecBlock.consNormal h1
      (ExecBlock.consRevert (ExecStmt.iteTrue (by simpa only [decide_eq_true hn] using hguard)
        (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure])))))))⟩

theorem uintToInt256Call {f : Frame} {evm : EVM.State} {w : UInt256} {e : Expr}
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (.int (Int.ofNat w.toNat)))
    (ret : Ident) :
    ExecStmt config f evm (.internalCall "SafeCast_toInt256" [e] ret)
      (if w.toNat < 2^255 then .ok {f with locals := f.locals.insert ret (.int (EVM.signed w))} evm
       else .reverted) := by
  let fc : Frame := {f with locals := (∅ : Store).insert "x" (.int (Int.ofNat w.toNat))}
  obtain ⟨f', hbody⟩ := uintToInt256Body (f := fc) (evm := evm) (store_get_self _ _ _)
  have hlookup : lookupCallable? f.contract "SafeCast_toInt256" = some uintToInt256Function.toCallable := by
    rw [hf]; exact uintToInt256_lookup
  by_cases hfit : w.toNat < 2^255
  · rw [if_pos hfit] at hbody ⊢
    exact internalCallFunctionReturn (evalExprs?_singleton he) hlookup rfl hbody
  · rw [if_neg hfit] at hbody ⊢
    exact internalCallFunctionRevert (evalExprs?_singleton he) hlookup rfl hbody

end Benchmarks.UniswapV4PoolManager

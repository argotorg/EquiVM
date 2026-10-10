import Benchmarks.UniswapV4PoolManager.FullMathSource
import Benchmarks.UniswapV4PoolManager.FullMathRoundWords
import Benchmarks.UniswapV4PoolManager.Values

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev fullMathRoundFunction : FunctionDecl := contract.functions[108]!
theorem fullMathRound_lookup : lookupCallable? contract "FullMath_mulDivRoundingUp" =
    some fullMathRoundFunction.toCallable := rfl

theorem fullMathRoundTail {f : Frame} {evm : EVM.State} {a b d : UInt256}
    (hfit : fullMathFits a b d)
    (ha : f.locals.get? "a" = some (.int (Int.ofNat a.toNat)))
    (hb : f.locals.get? "b" = some (.int (Int.ofNat b.toNat)))
    (hd : f.locals.get? "denominator" = some (.int (Int.ofNat d.toNat)))
    (hr : f.locals.get? "result" = some (.int (Int.ofNat (fullMathWord a b d).toNat))) :
    ∃ f', ExecFuncBody config f evm (fullMathRoundFunction.body.drop 3)
      (if fullMathRoundFits a b d then
        .returned f' evm (some [.int (Int.ofNat (fullMathRoundWord a b d).toNat)])
       else .reverted) := by
  have hrem := evalNeWords (evalWordMulMod
    (evalLocalValue (cfg := config) (f := f) (evm := evm) ha)
    (evalLocalValue hb) (evalLocalValue hd) (fullMathFits_ne hfit))
    (show evalExpr? config f evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by
      simp only [evalExpr?, pure]; rfl)
  change evalExpr? config f evm
    (.binary .ne (.binary .mod (.binary .mul (.var "a") (.var "b")) (.var "denominator")) (.intLit 0)) =
      .ok (.bool (decide (fullMathRemainder a b d ≠ ⟨0⟩))) at hrem
  by_cases hz : fullMathRemainder a b d = ⟨0⟩
  · have hround : fullMathRoundFits a b d := ⟨hfit, Or.inl hz⟩
    simp only [if_pos hround, fullMathRoundWord, if_pos hz]
    exact ⟨f, ExecFuncBody.execBlockRet (ExecBlock.consNormal
      (ExecStmt.iteFalse (by simpa only [hz, ne_self_iff_false, decide_false] using hrem) ExecBlock.nil)
      (ABlock.start.returns (evalLocalValue hr)))⟩
  · have he := evalWordAdd (evalLocalValue (cfg := config) (f := f) (evm := evm) hr)
      (show evalExpr? config f evm (.intLit 1) = .ok (.int (Int.ofNat (⟨1⟩ : UInt256).toNat)) by
        simp only [evalExpr?, pure]; rfl)
    let f1 := wordLocal f "result" (fullMathWord a b d + ⟨1⟩)
    have hadd : ExecStmt config f evm
        (.assign .localVar {base := "result"} (.cast (.binary .add (.var "result") (.intLit 1))
          (.elem (.int (.uint ⟨256, by decide⟩))))) (.ok f1 evm) :=
      ExecStmt.assign he (assignLocalValue hr)
    have hgt := evalWordGt (a := fullMathWord a b d + ⟨1⟩) (b := ⟨0⟩) (wordLocal_eval (cfg := config) (f := f) (evm := evm)
      (name := "result") (w := fullMathWord a b d + ⟨1⟩))
      (show evalExpr? config f1 evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by
        simp only [evalExpr?, pure]; rfl)
    by_cases ho : fullMathWord a b d + ⟨1⟩ = ⟨0⟩
    · have hround : ¬fullMathRoundFits a b d := fun hh => hh.2.elim hz (fun hn => hn ho)
      simp only [if_neg hround]
      refine ⟨f1, ExecFuncBody.execBlockRevert (ExecBlock.consRevert
        (ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using hrem)
          (ExecBlock.consNormal hadd (ExecBlock.consRevert (ExecStmt.requireFalse ?_)))))⟩
      simpa only [ho, Nat.lt_irrefl, decide_false] using hgt
    · have hpos : 0 < (fullMathWord a b d + ⟨1⟩).toNat := by
        by_contra hn
        apply ho
        apply u256_inj
        change (fullMathWord a b d + ⟨1⟩).toNat = 0
        omega
      have hround : fullMathRoundFits a b d := ⟨hfit, Or.inr ho⟩
      simp only [if_pos hround, fullMathRoundWord, if_neg hz]
      refine ⟨f1, ExecFuncBody.execBlockRet (ExecBlock.consNormal
        (ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using hrem)
          (ExecBlock.consNormal hadd (execBlock_singleton (ExecStmt.requireTrue ?_))))
        (ABlock.start.returns wordLocal_eval))⟩
      simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, decide_eq_true hpos] using hgt

theorem fullMathRoundBody {f : Frame} {evm : EVM.State} {a b d : UInt256}
    (hf : f.contract = contract)
    (ha : f.locals.get? "a" = some (.int (Int.ofNat a.toNat)))
    (hb : f.locals.get? "b" = some (.int (Int.ofNat b.toNat)))
    (hd : f.locals.get? "denominator" = some (.int (Int.ofNat d.toNat))) :
    ∃ f', ExecFuncBody config f evm fullMathRoundFunction.body
      (if fullMathRoundFits a b d then
        .returned f' evm (some [.int (Int.ofNat (fullMathRoundWord a b d).toNat)])
       else .reverted) := by
  let f0 := wordLocal f "result" ⟨0⟩
  let f1 := wordLocal f0 "__c0" (fullMathWord a b d)
  let f2 := wordLocal f1 "result" (fullMathWord a b d)
  have ha0 : f0.locals.get? "a" = some (.int (Int.ofNat a.toNat)) := by
    simp only [f0, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, ha]
  have hb0 : f0.locals.get? "b" = some (.int (Int.ofNat b.toNat)) := by
    simp only [f0, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hb]
  have hd0 : f0.locals.get? "denominator" = some (.int (Int.ofNat d.toNat)) := by
    simp only [f0, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hd]
  have h0 : ExecStmt config f evm fullMathRoundFunction.body[0]! (.ok f0 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have hcall := fullMathCall (f := f0) (evm := evm) hf (evalLocalValue ha0) (evalLocalValue hb0)
    (evalLocalValue hd0) "__c0"
  by_cases hfit : fullMathFits a b d
  · rw [if_pos hfit] at hcall
    have h2 : ExecStmt config f1 evm fullMathRoundFunction.body[2]! (.ok f2 evm) :=
      ExecStmt.assign wordLocal_eval (assignLocalValue
        ((store_get_ne _ _ (by decide : ("__c0" == "result") = false)).trans (store_get_self _ _ _)))
    obtain ⟨f3, htail⟩ := fullMathRoundTail (f := f2) (evm := evm) hfit
      (by simp only [f2, f1, f0, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, ha])
      (by simp only [f2, f1, f0, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hb])
      (by simp only [f2, f1, f0, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hd])
      (store_get_self _ _ _)
    exact ⟨f3, execFuncBody_prepend
      (ExecBlock.consNormal h0 (ExecBlock.consNormal hcall (execBlock_singleton h2))) htail⟩
  · rw [if_neg hfit] at hcall
    simp only [fullMathRoundFits, hfit, false_and, if_false]
    exact ⟨f0, ExecFuncBody.execBlockRevert (ExecBlock.consNormal h0 (ExecBlock.consRevert hcall))⟩

theorem fullMathRoundCall {f : Frame} {evm : EVM.State} {a b d : UInt256} {ea eb ed : Expr}
    (hf : f.contract = contract)
    (ha : evalExpr? config f evm ea = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? config f evm eb = .ok (.int (Int.ofNat b.toNat)))
    (hd : evalExpr? config f evm ed = .ok (.int (Int.ofNat d.toNat))) (ret : Ident) :
    ExecStmt config f evm (.internalCall "FullMath_mulDivRoundingUp" [ea, eb, ed] ret)
      (if fullMathRoundFits a b d then .ok (wordLocal f ret (fullMathRoundWord a b d)) evm else .reverted) := by
  let fc : Frame := {f with locals := ((((∅ : Store).insert "denominator"
    (.int (Int.ofNat d.toNat))).insert "b" (.int (Int.ofNat b.toNat))).insert
    "a" (.int (Int.ofNat a.toNat)))}
  obtain ⟨f', hbody⟩ := fullMathRoundBody (f := fc) (evm := evm) hf (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("a" == "b") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("b" == "denominator") = false)
      (by decide : ("a" == "denominator") = false)).trans (store_get_self _ _ _))
  have hargs : evalExprs? config f evm [ea, eb, ed] =
      .ok [.int (Int.ofNat a.toNat), .int (Int.ofNat b.toNat), .int (Int.ofNat d.toNat)] := by
    simp only [evalExprs?, ha, hb, hd, bind, EvalResult.bind, pure]
  have hlookup : lookupCallable? f.contract "FullMath_mulDivRoundingUp" = some fullMathRoundFunction.toCallable := by
    rw [hf]; exact fullMathRound_lookup
  by_cases hfit : fullMathRoundFits a b d
  · rw [if_pos hfit] at hbody ⊢
    exact internalCallFunctionReturn hargs hlookup rfl hbody
  · rw [if_neg hfit] at hbody ⊢
    exact internalCallFunctionRevert hargs hlookup rfl hbody

end Benchmarks.UniswapV4PoolManager

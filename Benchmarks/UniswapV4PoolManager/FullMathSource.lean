import Benchmarks.UniswapV4PoolManager.FullMathInverse
import Benchmarks.UniswapV4PoolManager.PoolCheckSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem fullMathBody {f : Frame} {evm : EVM.State} {a b d : UInt256}
    (ha : f.locals.get? "a" = some (.int (Int.ofNat a.toNat)))
    (hb : f.locals.get? "b" = some (.int (Int.ofNat b.toNat)))
    (hd : f.locals.get? "denominator" = some (.int (Int.ofNat d.toNat))) :
    ∃ f', ExecFuncBody config f evm fullMathFunction.body
      (if fullMathFits a b d then .returned f' evm (some [.int (Int.ofNat (fullMathWord a b d).toNat)])
       else .reverted) := by
  let f1 := fullMathPreludeFrame f a b
  have hpre := fullMathPrelude (evm := evm) ha hb
  have ha1 : f1.locals.get? "a" = some (.int (Int.ofNat a.toNat)) := by
    simp only [f1, fullMathPreludeFrame, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, ha]
  have hb1 : f1.locals.get? "b" = some (.int (Int.ofNat b.toNat)) := by
    simp only [f1, fullMathPreludeFrame, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hb]
  have hd1 : f1.locals.get? "denominator" = some (.int (Int.ofNat d.toNat)) := by
    simp only [f1, fullMathPreludeFrame, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hd]
  have hp0 : f1.locals.get? "prod0" = some (.int (Int.ofNat (fullMathLow a b).toNat)) := by
    simp only [f1, fullMathPreludeFrame, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte]
  have hp1 : f1.locals.get? "prod1" = some (.int (Int.ofNat (fullMathHigh a b).toNat)) := store_get_self _ _ _
  have hr : f1.locals.get? "result" = some (.int 0) := by
    simp only [f1, fullMathPreludeFrame, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte]; rfl
  have hguard := evalWordGt (evalLocalValue (cfg := config) (f := f1) (evm := evm) hd1)
    (evalLocalValue hp1)
  change evalExpr? config f1 evm (.binary .gt (.var "denominator") (.var "prod1")) =
    .ok (.bool (decide (fullMathFits a b d))) at hguard
  by_cases hfit : fullMathFits a b d
  · simp only [if_pos hfit]
    have h5 : ExecStmt config f1 evm fullMathFunction.body[5]! (.ok f1 evm) :=
      ExecStmt.requireTrue (by simpa only [decide_eq_true hfit] using hguard)
    have hzero := evalEqWords (evalLocalValue (cfg := config) (f := f1) (evm := evm) hp1)
      (show evalExpr? config f1 evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by
        simp only [evalExpr?, pure]; rfl)
    by_cases hz : fullMathHigh a b = ⟨0⟩
    · simp only [fullMathWord, if_pos hz]
      let f2 := wordLocal f1 "result" (UInt256.div (fullMathLow a b) d)
      have h6 : ExecStmt config f1 evm fullMathFunction.body[6]!
          (.returned f2 evm (some [.int (Int.ofNat (UInt256.div (fullMathLow a b) d).toNat)])) :=
        ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using hzero)
          (ExecBlock.consNormal (ExecStmt.assign (evalWordDiv (evalLocalValue hp0) (evalLocalValue hd1)
            (fullMathFits_ne hfit)) (assignLocalValue hr)) (ABlock.start.returns wordLocal_eval))
      exact ⟨f2, execFuncBody_prepend hpre (ExecFuncBody.execBlockRet
        (ExecBlock.consNormal h5 (ExecBlock.consReturn h6)))⟩
    · simp only [fullMathWord, if_neg hz]
      have h6 : ExecStmt config f1 evm fullMathFunction.body[6]! (.ok f1 evm) :=
        ExecStmt.iteFalse (by simpa only [decide_eq_false hz] using hzero) ExecBlock.nil
      let f2 := fullMathReduceFrame f1 a b d
      have hreduce := fullMathReduce (evm := evm) (fullMathFits_ne hfit) ha1 hb1 hd1 hp0 hp1
      have hd2 : f2.locals.get? "denominator" = some (.int (Int.ofNat (fullMathOdd d).toNat)) := by
        simp only [f2, fullMathReduceFrame, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte]
      have hp2 : f2.locals.get? "prod0" = some (.int (Int.ofNat (fullMathWide a b d).toNat)) := store_get_self _ _ _
      have hr2 : f2.locals.get? "result" = some (.int 0) := by
        simp only [f2, fullMathReduceFrame, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hr]
      obtain ⟨f3, hinv⟩ := fullMathInverseBody (f := f2) (evm := evm) hd2 hp2 hr2
      exact ⟨f3, execFuncBody_prepend hpre (execFuncBody_prepend
        (ExecBlock.consNormal h5 (execBlock_singleton h6)) (execFuncBody_prepend hreduce hinv))⟩
  · simp only [if_neg hfit]
    exact ⟨f1, execFuncBody_prepend hpre (ExecFuncBody.execBlockRevert (ExecBlock.consRevert
      (ExecStmt.requireFalse (by simpa only [decide_eq_false hfit] using hguard))))⟩

theorem fullMathCall {f : Frame} {evm : EVM.State} {a b d : UInt256} {ea eb ed : Expr}
    (hf : f.contract = contract)
    (ha : evalExpr? config f evm ea = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? config f evm eb = .ok (.int (Int.ofNat b.toNat)))
    (hd : evalExpr? config f evm ed = .ok (.int (Int.ofNat d.toNat))) (ret : Ident) :
    ExecStmt config f evm (.internalCall "FullMath_mulDiv" [ea, eb, ed] ret)
      (if fullMathFits a b d then .ok (wordLocal f ret (fullMathWord a b d)) evm else .reverted) := by
  let fc : Frame := {f with locals := ((((∅ : Store).insert "denominator"
    (.int (Int.ofNat d.toNat))).insert "b" (.int (Int.ofNat b.toNat))).insert
    "a" (.int (Int.ofNat a.toNat)))}
  obtain ⟨f', hbody⟩ := fullMathBody (f := fc) (evm := evm) (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("a" == "b") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("b" == "denominator") = false)
      (by decide : ("a" == "denominator") = false)).trans (store_get_self _ _ _))
  have hargs : evalExprs? config f evm [ea, eb, ed] =
      .ok [.int (Int.ofNat a.toNat), .int (Int.ofNat b.toNat), .int (Int.ofNat d.toNat)] := by
    simp only [evalExprs?, ha, hb, hd, bind, EvalResult.bind, pure]
  have hlookup : lookupCallable? f.contract "FullMath_mulDiv" = some fullMathFunction.toCallable := by
    rw [hf]; exact fullMath_lookup
  by_cases hfit : fullMathFits a b d
  · rw [if_pos hfit] at hbody ⊢
    exact internalCallFunctionReturn hargs hlookup rfl hbody
  · rw [if_neg hfit] at hbody ⊢
    exact internalCallFunctionRevert hargs hlookup rfl hbody

end Benchmarks.UniswapV4PoolManager

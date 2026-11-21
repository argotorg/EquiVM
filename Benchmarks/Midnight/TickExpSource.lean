import Benchmarks.Midnight.TickExpModel

/-! Source execution of the nonnegative branch of the exponential helper. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def wExpPositiveFrame (frame : Frame) (x : Int) : Frame :=
  { frame with locals := ((((((frame.locals.insert "ln2" (.int 693147180559945309)).insert
    "offset" (.int 322611214989459870)).insert "q" (.int (wExpQ x))).insert
    "r" (.int (wExpR x))).insert "secondTerm" (.int (wExpSecond x))).insert
    "thirdTerm" (.int (wExpThird x))).insert "expR" (.int (wExpMantissa x)) }

theorem wExpPositiveBody_source {cfg : Config} {frame : Frame} {evm : State} {x : Int}
    (hx : frame.locals.get? "x" = some (.int x)) :
    ExecBlock cfg frame evm wExpPositiveBody
      (.returned (wExpPositiveFrame frame x) evm (some [.int (wExpPositiveValue x)])) := by
  simp only [Std.HashMap.get?_eq_getElem?] at hx
  let f1 := { frame with locals := frame.locals.insert "ln2" (.int 693147180559945309) }
  let f2 := { f1 with locals := f1.locals.insert "offset" (.int 322611214989459870) }
  let f3 := { f2 with locals := f2.locals.insert "q" (.int (wExpQ x)) }
  let f4 := { f3 with locals := f3.locals.insert "r" (.int (wExpR x)) }
  let f5 := { f4 with locals := f4.locals.insert "secondTerm" (.int (wExpSecond x)) }
  let f6 := { f5 with locals := f5.locals.insert "thirdTerm" (.int (wExpThird x)) }
  have hp1 : ABlock cfg evm frame wExpPositiveBody f1 (wExpPositiveBody.drop 1) :=
    ABlock.start.letStep (by simp only [evalExpr?, pure])
  have hp2 : ABlock cfg evm frame wExpPositiveBody f2 (wExpPositiveBody.drop 2) :=
    hp1.letStep (by simp only [evalExpr?, pure])
  have hp3 : ABlock cfg evm frame wExpPositiveBody f3 (wExpPositiveBody.drop 3) :=
    hp2.letStep (by
      simp [evalExpr?, f2, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        Std.HashMap.getElem_insert, hx, EvalResult.ofOption,
        bind, pure, EvalResult.bind, evalBinaryOp?, castValue_int, wExpQ])
  have hp4 : ABlock cfg evm frame wExpPositiveBody f4 (wExpPositiveBody.drop 4) :=
    hp3.letStep (by
      simp [evalExpr?, f3, f2, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        Std.HashMap.getElem_insert, hx, EvalResult.ofOption,
        bind, pure, EvalResult.bind, evalBinaryOp?, castValue_int, wExpR])
  have hp5 : ABlock cfg evm frame wExpPositiveBody f5 (wExpPositiveBody.drop 5) :=
    hp4.letStep (by
      simp [evalExpr?, f4, f3, f2, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        Std.HashMap.getElem_insert, hx, EvalResult.ofOption,
        bind, pure, EvalResult.bind, evalBinaryOp?, castValue_int, wExpSecond])
  have hp6 : ABlock cfg evm frame wExpPositiveBody f6 (wExpPositiveBody.drop 6) :=
    hp5.letStep (by
      simp [evalExpr?, f5, f4, f3, f2, f1, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, hx, EvalResult.ofOption,
        bind, pure, EvalResult.bind, evalBinaryOp?, castValue_int, wExpThird])
  have hp7 : ABlock cfg evm frame wExpPositiveBody
      (wExpPositiveFrame frame x) (wExpPositiveBody.drop 7) :=
    hp6.letStep (by
      simp [evalExpr?, f6, f5, f4, f3, f2, f1, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, hx, EvalResult.ofOption,
        bind, pure, EvalResult.bind, evalBinaryOp?, castValue_int, wExpMantissa])
  apply hp7.run
  apply ExecBlock.consReturn
  apply ExecStmt.return
  have hn : ¬ tickUnsigned (wExpQ x) < 0 := by
    change ¬ normalizeInt (.uint ⟨256, by decide⟩) (wExpQ x) < 0
    unfold normalizeInt
    exact not_lt.mpr (Int.emod_nonneg _ (by decide))
  simp [evalExprs?, evalExpr?, wExpPositiveFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert,
    EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?, castValue_int,
    IntType.bitWidth, hn, wExpPositiveValue]
  split_ifs <;> rfl

theorem wExpSource_nonnegative {cfg : Config} {frame : Frame} {evm : State} {x : Int}
    (hx : frame.locals.get? "x" = some (.int x)) (hn : 0 ≤ x) :
    ExecFuncBody cfg frame evm wExpFunction.body
      (.returned (wExpPositiveFrame frame x) evm (some [.int (wExpPositiveValue x)])) := by
  apply ExecFuncBody.execBlockRet
  rw [wExpFunction_body]
  apply ExecBlock.consReturn
  apply ExecStmt.iteFalse
  · simp only [evalExpr?, hx, EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?,
      decide_eq_false (by omega : ¬ x < 0)]
  · exact wExpPositiveBody_source hx

theorem callWExp_nonnegative {cfg : Config} {frame : Frame} {evm : State}
    {x : Int} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract) (he : evalExprs? cfg frame evm args = .ok [.int x])
    (hn : 0 ≤ x) :
    ExecStmt cfg frame evm (.internalCall "TickLib_wExp" args name)
      (.ok (resumeAfterInternalCall frame name (some [.int (wExpPositiveValue x)])) evm) := by
  apply internalCallFunctionReturn (callee := wExpFunction)
    (locals := (∅ : Store).insert "x" (.int x)) he
  · rw [hc]; rfl
  · rfl
  · exact wExpSource_nonnegative (store_get_self _ _ _) hn

theorem wExpSource {cfg : Config} {frame : Frame} {evm : State} {x : Int}
    (hc : frame.contract = contract) (hx : frame.locals.get? "x" = some (.int x))
    (hinner : x < 0 → 0 ≤ tickSigned (0 - x))
    (hnz : x < 0 → wExpPositiveValue (tickSigned (0 - x)) ≠ 0) :
    ∃ frame', ExecFuncBody cfg frame evm wExpFunction.body
      (.returned frame' evm (some [.int (wExpValue x)])) := by
  by_cases hneg : x < 0
  · let inner := tickSigned (0 - x)
    let final := resumeAfterInternalCall frame "__c0" (some [.int (wExpPositiveValue inner)])
    have hcall : ExecStmt cfg frame evm
        (.internalCall "TickLib_wExp"
          [.cast (.binary .sub (.intLit 0) (.var "x")) (.elem (.int (.sint ⟨256, by decide⟩)))]
          "__c0") (.ok final evm) :=
      callWExp_nonnegative hc (by
        simp only [evalExprs?, evalExpr?, hx, EvalResult.ofOption, bind, pure, EvalResult.bind,
          evalBinaryOp?, castValue_int]
        rfl) (hinner hneg)
    refine ⟨final, ExecFuncBody.execBlockRet ?_⟩
    rw [wExpFunction_body]
    apply ExecBlock.consReturn
    apply ExecStmt.iteTrue
    · simp only [evalExpr?, hx, EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?,
        decide_eq_true hneg]
    · refine ExecBlock.consNormal hcall (ExecBlock.consReturn (ExecStmt.return ?_))
      simp only [evalExprs?, evalExpr?, final, inner, resumeAfterInternalCall, collapseReturns,
        store_get_self, EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?,
        if_neg (hnz hneg), wExpValue, if_pos hneg]
  · exact ⟨_, by simpa only [wExpValue, if_neg hneg] using wExpSource_nonnegative hx (by omega)⟩

theorem callWExp {cfg : Config} {frame : Frame} {evm : State}
    {x : Int} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract) (he : evalExprs? cfg frame evm args = .ok [.int x])
    (hinner : x < 0 → 0 ≤ tickSigned (0 - x))
    (hnz : x < 0 → wExpPositiveValue (tickSigned (0 - x)) ≠ 0) :
    ExecStmt cfg frame evm (.internalCall "TickLib_wExp" args name)
      (.ok (resumeAfterInternalCall frame name (some [.int (wExpValue x)])) evm) := by
  obtain ⟨frame', hbody⟩ := wExpSource (cfg := cfg) (evm := evm)
    (frame := { frame with locals := (∅ : Store).insert "x" (.int x) })
    hc (store_get_self _ _ _) hinner hnz
  exact internalCallFunctionReturn he (by rw [hc]; rfl) rfl hbody

end Benchmarks.Midnight

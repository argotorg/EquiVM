import Benchmarks.UniswapV4PoolManager.SimpleMulDivWords
import Benchmarks.UniswapV4PoolManager.ValueLocals
import Benchmarks.UniswapV4PoolManager.PoolCheckSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev simpleMulDivFunction : FunctionDecl := contract.functions[78]!
theorem simpleMulDiv_lookup : lookupCallable? contract "UnsafeMath_simpleMulDiv" = some simpleMulDivFunction.toCallable := rfl

theorem simpleMulDiv_eval {cfg : Config} {f : Frame} {evm : State}
    {ea eb ed : Expr} {a b denominator : UInt256}
    (ha : evalExpr? cfg f evm ea = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg f evm eb = .ok (.int (Int.ofNat b.toNat)))
    (hd : evalExpr? cfg f evm ed = .ok (.int (Int.ofNat denominator.toNat))) :
    evalExpr? cfg f evm (.ite (.binary .eq ed (.intLit 0)) (.intLit 0)
      (.binary .div (.cast (.binary .mul ea eb) (.elem (.int (.uint ⟨256, by decide⟩)))) ed)) =
      .ok (.int (Int.ofNat (simpleMulDiv a b denominator).toNat)) := by
  have hz : evalExpr? cfg f evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp only [evalExpr?, pure]; rfl
  have hg := evalEqWords hd hz
  rw [evalExpr?, hg]
  by_cases hzero : denominator = ⟨0⟩
  · simp only [bind, EvalResult.bind, hz, hzero, decide_true, simpleMulDiv_zero]
  · simp only [decide_eq_false hzero, bind, EvalResult.bind]
    exact evalWordDiv (evalWordMul ha hb) hd hzero

theorem simpleMulDivBody {f : Frame} {evm : State} {a b denominator : UInt256}
    (ha : f.locals.get? "a" = some (.int (Int.ofNat a.toNat)))
    (hb : f.locals.get? "b" = some (.int (Int.ofNat b.toNat)))
    (hd : f.locals.get? "denominator" = some (.int (Int.ofNat denominator.toNat))) :
    ∃ f', ExecFuncBody config f evm simpleMulDivFunction.body
      (.returned f' evm (some [.int (Int.ofNat (simpleMulDiv a b denominator).toNat)])) := by
  let f1 := valueLocal f "result" (.int 0)
  let f2 := valueLocal f1 "result" (.int (Int.ofNat (simpleMulDiv a b denominator).toNat))
  have ha1 : f1.locals.get? "a" = some (.int (Int.ofNat a.toNat)) :=
    (store_get_ne _ _ (by decide : ("result" == "a") = false)).trans ha
  have hb1 : f1.locals.get? "b" = some (.int (Int.ofNat b.toNat)) :=
    (store_get_ne _ _ (by decide : ("result" == "b") = false)).trans hb
  have hd1 : f1.locals.get? "denominator" = some (.int (Int.ofNat denominator.toNat)) :=
    (store_get_ne _ _ (by decide : ("result" == "denominator") = false)).trans hd
  have he := simpleMulDiv_eval (evalLocalValue (cfg := config) (evm := evm) ha1) (evalLocalValue hb1) (evalLocalValue hd1)
  refine ⟨f2, .execBlockRet ?_⟩
  exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure]))
    (ExecBlock.consNormal (ExecStmt.assign he (assignLocalValue (store_get_self _ _ _)))
      (ABlock.start.returns (evalLocalValue (store_get_self _ _ _))))

theorem simpleMulDivCall {f : Frame} {evm : State} {a b denominator : UInt256} {ea eb ed : Expr}
    (hf : f.contract = contract)
    (ha : evalExpr? config f evm ea = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? config f evm eb = .ok (.int (Int.ofNat b.toNat)))
    (hd : evalExpr? config f evm ed = .ok (.int (Int.ofNat denominator.toNat))) (ret : Ident) :
    ExecStmt config f evm (.internalCall "UnsafeMath_simpleMulDiv" [ea, eb, ed] ret)
      (.ok (valueLocal f ret (.int (Int.ofNat (simpleMulDiv a b denominator).toNat))) evm) := by
  let fc : Frame := {f with locals :=
    ((((∅ : Store).insert "denominator" (.int (Int.ofNat denominator.toNat))).insert
      "b" (.int (Int.ofNat b.toNat))).insert "a" (.int (Int.ofNat a.toNat)))}
  obtain ⟨f', hbody⟩ := simpleMulDivBody (f := fc) (evm := evm) (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("a" == "b") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("b" == "denominator") = false)
      (by decide : ("a" == "denominator") = false)).trans (store_get_self _ _ _))
  exact internalCallFunctionReturn
    (argVals := [.int (Int.ofNat a.toNat), .int (Int.ofNat b.toNat), .int (Int.ofNat denominator.toNat)])
    (value := some [.int (Int.ofNat (simpleMulDiv a b denominator).toNat)])
    (by simp only [evalExprs?, ha, hb, hd, bind, EvalResult.bind, pure])
    (by rw [hf]; exact simpleMulDiv_lookup) rfl hbody

end Benchmarks.UniswapV4PoolManager

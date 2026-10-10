import Benchmarks.UniswapV4PoolManager.SignedQuotientSource
import Benchmarks.UniswapV4PoolManager.CallComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev tickSpacingFunction : FunctionDecl := contract.functions[62]!
theorem tickSpacing_lookup : lookupCallable? contract "Pool_tickSpacingToMaxLiquidityPerTick" =
    some tickSpacingFunction.toCallable := rfl

def tickSpacingMin (spacing : Int) : Int :=
  if spacing = 0 then 0 else (-887272 : Int).tdiv spacing - if (-887272 : Int).tmod spacing < 0 then 1 else 0
def tickSpacingMax (spacing : Int) : Int := if spacing = 0 then 0 else (887272 : Int).tdiv spacing
def tickSpacingCount (spacing : Int) : Int :=
  normalizeInt (.uint ⟨256, by decide⟩) (tickSpacingMax spacing-tickSpacingMin spacing+1)
def tickSpacingLimit (spacing : Int) : Int :=
  if tickSpacingCount spacing = 0 then 0 else
    normalizeInt (.uint ⟨128, by decide⟩) ((2^128-1)/tickSpacingCount spacing)

theorem tickSpacingMin_eval {f : Frame} {evm : EVM.State} {spacing : Int}
    (hs : f.locals.get? "tickSpacing" = some (.int spacing)) (hn : spacing ≠ 0) :
    evalExpr? config f evm (.binary .sub
      (.binary .sdiv (.unary .neg (.intLit 887272)) (.var "tickSpacing"))
      (.ite (.binary .lt (.binary .srem (.unary .neg (.intLit 887272)) (.var "tickSpacing"))
        (.intLit 0)) (.intLit 1) (.intLit 0))) = .ok (.int (tickSpacingMin spacing)) := by
  have hc : evalExpr? config f evm (.unary .neg (.intLit 887272)) = .ok (.int (-887272)) := by
    simp only [evalExpr?, bind, EvalResult.bind, pure, evalUnaryOp?, EvalResult.ofOption]
  simpa only [tickSpacingMin, if_neg hn] using evalSignedQuotientCorrection hc (evalLocalValue hs) hn

theorem tickSpacingPrelude {f : Frame} {evm : EVM.State} {spacing : Int}
    (hs : f.locals.get? "tickSpacing" = some (.int spacing)) :
    ∃ f', ExecBlock config f evm (tickSpacingFunction.body.take 3) (.ok f' evm) ∧
      f'.locals.get? "minTick" = some (.int (tickSpacingMin spacing)) ∧
      f'.locals.get? "maxTick" = some (.int (tickSpacingMax spacing)) := by
  let f1 : Frame := {f with locals := f.locals.insert "minTick" (.int 0)}
  let f2 : Frame := {f1 with locals := f1.locals.insert "maxTick" (.int 0)}
  have hp : ExecBlock config f evm (tickSpacingFunction.body.take 2) (.ok f2 evm) :=
    ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure]))
      (execBlock_singleton (ExecStmt.letDecl (by simp only [evalExpr?, pure])))
  have hs2 : f2.locals.get? "tickSpacing" = some (.int spacing) :=
    (store_get_ne2 _ _ _ (by decide : ("minTick" == "tickSpacing") = false)
      (by decide : ("maxTick" == "tickSpacing") = false)).trans hs
  have hcond : evalExpr? config f2 evm (.binary .ne (.var "tickSpacing") (.intLit 0)) =
      .ok (.bool (decide (spacing ≠ 0))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hs2]
    simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?, BEq.beq, Value.int.injEq,
      decide_not]
  by_cases hn : spacing = 0
  · rw [decide_eq_false (by simpa using hn)] at hcond
    refine ⟨f2, execBlock_append hp (execBlock_singleton (ExecStmt.iteFalse hcond ExecBlock.nil)), ?_, ?_⟩
    · rw [tickSpacingMin, if_pos hn]
      exact (store_get_ne _ _ (by decide : ("maxTick" == "minTick") = false)).trans (store_get_self _ _ _)
    · rw [tickSpacingMax, if_pos hn]
      exact store_get_self _ _ _
  · rw [decide_eq_true hn] at hcond
    let f3 : Frame := {f2 with locals := f2.locals.insert "minTick" (.int (tickSpacingMin spacing))}
    let f4 : Frame := {f3 with locals := f3.locals.insert "maxTick" (.int (tickSpacingMax spacing))}
    have hmin : ExecStmt config f2 evm (.assign .localVar {base := "minTick"} _ ) (.ok f3 evm) :=
      ExecStmt.assign (tickSpacingMin_eval hs2 hn) (assignLocalValue
        ((store_get_ne _ _ (by decide : ("maxTick" == "minTick") = false)).trans (store_get_self _ _ _)))
    have hmax : ExecStmt config f3 evm (.assign .localVar {base := "maxTick"}
        (.binary .sdiv (.intLit 887272) (.var "tickSpacing"))) (.ok f4 evm) := by
      apply ExecStmt.assign _ (assignLocalValue
        ((store_get_ne _ _ (by decide : ("minTick" == "maxTick") = false)).trans (store_get_self _ _ _)))
      rw [tickSpacingMax, if_neg hn]
      exact evalSignedDiv (by simp only [evalExpr?, pure]) (evalLocalValue
        ((store_get_ne _ _ (by decide : ("minTick" == "tickSpacing") = false)).trans hs2)) hn
    exact ⟨f4, execBlock_append hp (execBlock_singleton (ExecStmt.iteTrue hcond
      (ExecBlock.consNormal hmin (execBlock_singleton hmax)))),
      (store_get_ne _ _ (by decide : ("maxTick" == "minTick") = false)).trans (store_get_self _ _ _),
      store_get_self _ _ _⟩

theorem tickSpacingBody {f : Frame} {evm : EVM.State} {spacing : Int}
    (hs : f.locals.get? "tickSpacing" = some (.int spacing)) :
    ∃ f', ExecFuncBody config f evm tickSpacingFunction.body
      (.returned f' evm (some [.int (tickSpacingLimit spacing)])) := by
  obtain ⟨f3, hp, hlo, hhi⟩ := tickSpacingPrelude (evm := evm) hs
  let f4 : Frame := {f3 with locals := f3.locals.insert "numTicks" (.int (tickSpacingCount spacing))}
  have hsub : evalExpr? config f3 evm (.binary .sub (.var "maxTick") (.var "minTick")) =
      .ok (.int (tickSpacingMax spacing-tickSpacingMin spacing)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hhi, evalLocalValue hlo]
    rfl
  have hsum : evalExpr? config f3 evm (.binary .add (.binary .sub (.var "maxTick") (.var "minTick")) (.intLit 1)) =
      .ok (.int (tickSpacingMax spacing-tickSpacingMin spacing+1)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hsub]
    simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?]
  have hn : ExecStmt config f3 evm tickSpacingFunction.body[3]! (.ok f4 evm) :=
    ExecStmt.letDecl (evalExpr_cast_int hsum)
  have heq := evalIntEq (evalLocalValue (cfg := config) (evm := evm) (f := f4)
      (store_get_self _ _ _))
    (show evalExpr? config f4 evm (.intLit 0) = .ok (.int 0) by simp only [evalExpr?, pure])
  have hret : evalExpr? config f4 evm
      (.ite (.binary .eq (.var "numTicks") (.intLit 0)) (.intLit 0)
        (.cast (.binary .div (.intLit (2^128-1)) (.var "numTicks")) (.elem (.int (.uint ⟨128, by decide⟩))))) =
      .ok (.int (tickSpacingLimit spacing)) := by
    rw [evalExpr?, heq]
    by_cases hz : tickSpacingCount spacing = 0
    · simp only [tickSpacingLimit, if_pos hz, decide_eq_true hz, bind, EvalResult.bind, evalExpr?, pure]
    · simp only [tickSpacingLimit, if_neg hz, decide_eq_false hz, bind, EvalResult.bind]
      apply evalExpr_cast_int
      rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue (store_get_self _ _ _)]
      simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?, if_neg hz]
  exact ⟨f4, execFuncBody_prepend hp (.execBlockRet
    (ExecBlock.consNormal hn (ABlock.start.returns hret)))⟩

theorem tickSpacingCall {f : Frame} {evm : EVM.State} {e : Expr} {spacing : Int}
    (hf : f.contract = contract) (hs : evalExpr? config f evm e = .ok (.int spacing)) (ret : Ident) :
    ExecStmt config f evm (.internalCall "Pool_tickSpacingToMaxLiquidityPerTick" [e] ret)
      (.ok {f with locals := f.locals.insert ret (.int (tickSpacingLimit spacing))} evm) := by
  obtain ⟨f', hb⟩ := tickSpacingBody (f := {f with locals := (∅ : Store).insert "tickSpacing" (.int spacing)})
    (evm := evm) (store_get_self _ _ _)
  exact internalCallFunctionReturn (evalExprs?_singleton hs)
    (by rw [hf]; exact tickSpacing_lookup) rfl hb

end Benchmarks.UniswapV4PoolManager

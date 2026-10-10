import Benchmarks.UniswapV4PoolManager.TickBitmapArithmetic
import Benchmarks.UniswapV4PoolManager.SignedDivisionSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev tickBitmapFunction : FunctionDecl := contract.functions[63]!
theorem tickBitmap_lookup : lookupCallable? contract "TickBitmap_flipTick" = some tickBitmapFunction.toCallable := rfl

def tickBitmapPreludeFrame (f : Frame) (tick spacing : Int) : Frame :=
  let f1 : Frame := {f with locals := f.locals.insert "compressed" (.int 0)}
  if spacing = 0 then f1 else {f1 with locals := f1.locals.insert "compressed" (.int (tickBitmapCompressed tick spacing))}

theorem tickBitmapPreludeFrame_get {f : Frame} {tick spacing : Int} {name : Ident}
    (hn : ("compressed" == name) = false) :
    (tickBitmapPreludeFrame f tick spacing).locals.get? name = f.locals.get? name := by
  unfold tickBitmapPreludeFrame
  split
  · exact store_get_ne _ _ hn
  · exact (store_get_ne _ _ hn).trans (store_get_ne _ _ hn)

theorem tickBitmapPreludeFrame_compressed (f : Frame) (tick spacing : Int) :
    (tickBitmapPreludeFrame f tick spacing).locals.get? "compressed" = some (.int (tickBitmapCompressed tick spacing)) := by
  unfold tickBitmapPreludeFrame
  split
  · rename_i hz
    simp only [tickBitmapCompressed, hz, Int.tdiv_zero]
    exact store_get_self _ _ _
  · exact store_get_self _ _ _

theorem tickBitmapPrelude {f : Frame} {evm : EVM.State} {tick spacing : Int}
    (ht : f.locals.get? "tick" = some (.int tick))
    (hs : f.locals.get? "tickSpacing" = some (.int spacing)) :
    ExecBlock config f evm (tickBitmapFunction.body.take 2)
      (if tickBitmapAligned tick spacing then .ok (tickBitmapPreludeFrame f tick spacing) evm else .reverted) := by
  let f1 : Frame := {f with locals := f.locals.insert "compressed" (.int 0)}
  have hlet : ExecStmt config f evm tickBitmapFunction.body[0]! (.ok f1 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure])
  have ht1 : f1.locals.get? "tick" = some (.int tick) :=
    (store_get_ne _ _ (by decide : ("compressed" == "tick") = false)).trans ht
  have hs1 : f1.locals.get? "tickSpacing" = some (.int spacing) :=
    (store_get_ne _ _ (by decide : ("compressed" == "tickSpacing") = false)).trans hs
  have hcond : evalExpr? config f1 evm (.binary .ne (.var "tickSpacing") (.intLit 0)) =
      .ok (.bool (decide (spacing ≠ 0))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hs1]
    simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?, BEq.beq, Value.int.injEq, decide_not]
  by_cases hz : spacing = 0
  · rw [if_pos (.inl hz), tickBitmapPreludeFrame, if_pos hz]
    rw [decide_eq_false (by simpa using hz)] at hcond
    exact ExecBlock.consNormal hlet (execBlock_singleton (ExecStmt.iteFalse hcond ExecBlock.nil))
  · rw [decide_eq_true hz] at hcond
    have hr := evalSignedRem (evalLocalValue (cfg := config) (evm := evm) ht1) (evalLocalValue hs1) hz
    have heq := evalIntEq hr
      (show evalExpr? config f1 evm (.intLit 0) = .ok (.int 0) by simp only [evalExpr?, pure])
    by_cases ha : tick.tmod spacing = 0
    · rw [if_pos (.inr ha), tickBitmapPreludeFrame, if_neg hz]
      rw [decide_eq_true ha] at heq
      exact ExecBlock.consNormal hlet (execBlock_singleton (ExecStmt.iteTrue hcond
        (ExecBlock.consNormal (ExecStmt.requireTrue heq) (execBlock_singleton
          (ExecStmt.assign (evalSignedDiv (evalLocalValue ht1) (evalLocalValue hs1) hz)
            (assignLocalValue (store_get_self _ _ _)))))))
    · rw [if_neg (by exact fun h => h.elim hz ha)]
      rw [decide_eq_false ha] at heq
      exact ExecBlock.consNormal hlet (ExecBlock.consRevert (ExecStmt.iteTrue hcond
        (ExecBlock.consRevert (ExecStmt.requireFalse heq))))

end Benchmarks.UniswapV4PoolManager

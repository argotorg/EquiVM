import Benchmarks.UniswapV4PoolManager.PoolSwapDeltaWords
import Benchmarks.UniswapV4PoolManager.ValueLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapDeltaFrame (f : Frame) (cf : Bool) (specified remaining calculated : UInt256) : Frame :=
  let f1 := valueLocal f (poolSwapDeltaName0 cf) (.int (EVM.signed (poolSwapDeltaArg cf specified remaining calculated)))
  let f2 := valueLocal f1 (poolSwapDeltaName1 cf) (.int (EVM.signed (poolSwapDeltaArg (!cf) specified remaining calculated)))
  let f3 := valueLocal f2 (poolSwapDeltaName2 cf) (.int (EVM.signed (poolSwapDeltaWord cf specified remaining calculated)))
  valueLocal f3 "swapDelta" (.int (EVM.signed (poolSwapDeltaWord cf specified remaining calculated)))

theorem poolSwapDeltaFrame_get (f : Frame) (cf : Bool) (specified remaining calculated : UInt256) (key : Ident)
    (h0 : (poolSwapDeltaName0 cf == key) = false) (h1 : (poolSwapDeltaName1 cf == key) = false)
    (h2 : (poolSwapDeltaName2 cf == key) = false) (hd : ("swapDelta" == key) = false) :
    (poolSwapDeltaFrame f cf specified remaining calculated).locals.get? key = f.locals.get? key := by
  simp only [poolSwapDeltaFrame, valueLocal_get, h0, h1, h2, hd, Bool.false_eq_true, if_false]

theorem poolSwapDeltaFrame_delta (f : Frame) (cf : Bool) (specified remaining calculated : UInt256) :
    (poolSwapDeltaFrame f cf specified remaining calculated).locals.get? "swapDelta" =
      some (.int (EVM.signed (poolSwapDeltaWord cf specified remaining calculated))) := store_get_self _ _ _

theorem poolSwapDeltaExpr_eval {f : Frame} {evm : State} {p : PoolSwapParamsWords} {remaining calculated : UInt256}
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p))
    (hr : f.locals.get? "amountSpecifiedRemaining" = some (.int (EVM.signed remaining)))
    (hc : f.locals.get? "amountCalculated" = some (.int (EVM.signed calculated))) (cf : Bool) :
    evalExpr? config f evm (poolSwapDeltaExpr cf) =
      .ok (.int (EVM.signed (poolSwapDeltaArg cf p.amountSpecified remaining calculated))) := by
  cases cf
  · exact evalSignedWordSub (evalStructField (field := "amountSpecified") (evalLocalValue hp) rfl) (evalLocalValue hr)
  · exact evalLocalValue hc

theorem poolSwapDeltaBranchSource {f : Frame} {evm : State} {p : PoolSwapParamsWords} {remaining calculated : UInt256}
    {old : Value} (cf : Bool) (hf : f.contract = contract)
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p))
    (hr : f.locals.get? "amountSpecifiedRemaining" = some (.int (EVM.signed remaining)))
    (hc : f.locals.get? "amountCalculated" = some (.int (EVM.signed calculated)))
    (hd : f.locals.get? "swapDelta" = some old) :
    ExecBlock config f evm (poolSwapDeltaBranch cf)
      (if poolSwapDeltaFits cf p.amountSpecified remaining calculated then
        .ok (poolSwapDeltaFrame f cf p.amountSpecified remaining calculated) evm else .reverted) := by
  let a := poolSwapDeltaArg cf p.amountSpecified remaining calculated
  let b := poolSwapDeltaArg (!cf) p.amountSpecified remaining calculated
  let f1 := valueLocal f (poolSwapDeltaName0 cf) (.int (EVM.signed a))
  let f2 := valueLocal f1 (poolSwapDeltaName1 cf) (.int (EVM.signed b))
  let f3 := valueLocal f2 (poolSwapDeltaName2 cf) (.int (EVM.signed (balanceDeltaWord a b)))
  have hfirst := signedToInt128Call hf (poolSwapDeltaExpr_eval (evm := evm) hp hr hc cf) (poolSwapDeltaName0 cf)
  by_cases ha : signedFits ⟨128, by decide⟩ (EVM.signed a)
  · rw [if_pos ha] at hfirst
    have hp1 : f1.locals.get? "params" = some (poolSwapParamsValue p) :=
      (store_get_ne _ _ (by cases cf <;> decide : (poolSwapDeltaName0 cf == "params") = false)).trans hp
    have hr1 : f1.locals.get? "amountSpecifiedRemaining" = some (.int (EVM.signed remaining)) :=
      (store_get_ne _ _ (by cases cf <;> decide : (poolSwapDeltaName0 cf == "amountSpecifiedRemaining") = false)).trans hr
    have hc1 : f1.locals.get? "amountCalculated" = some (.int (EVM.signed calculated)) :=
      (store_get_ne _ _ (by cases cf <;> decide : (poolSwapDeltaName0 cf == "amountCalculated") = false)).trans hc
    have hsecond := signedToInt128Call (f := f1) hf (poolSwapDeltaExpr_eval (evm := evm) hp1 hr1 hc1 (!cf)) (poolSwapDeltaName1 cf)
    by_cases hb : signedFits ⟨128, by decide⟩ (EVM.signed b)
    · rw [if_pos hb] at hsecond
      rw [if_pos (show poolSwapDeltaFits cf p.amountSpecified remaining calculated from ⟨ha, hb⟩)]
      have hpack : ExecStmt config f2 evm
          (.internalCall "toBalanceDelta" [.var (poolSwapDeltaName0 cf), .var (poolSwapDeltaName1 cf)] (poolSwapDeltaName2 cf))
          (.ok f3 evm) :=
        balanceDeltaCall (f := f2) hf
          (evalLocalValue ((store_get_ne _ _ (by cases cf <;> decide : (poolSwapDeltaName1 cf == poolSwapDeltaName0 cf) = false)).trans
            (store_get_self _ _ _))) (evalLocalValue (store_get_self _ _ _)) (poolSwapDeltaName2 cf)
      have hd3 : f3.locals.get? "swapDelta" = some old :=
        (store_get_ne3 _ _ _ _ (by cases cf <;> decide : (poolSwapDeltaName0 cf == "swapDelta") = false)
          (by cases cf <;> decide : (poolSwapDeltaName1 cf == "swapDelta") = false)
          (by cases cf <;> decide : (poolSwapDeltaName2 cf == "swapDelta") = false)).trans hd
      exact ExecBlock.consNormal hfirst (ExecBlock.consNormal hsecond (ExecBlock.consNormal hpack
        (execBlock_singleton (ExecStmt.assign (evalLocalValue (store_get_self _ _ _)) (assignLocalValue hd3)))))
    · rw [if_neg (show ¬poolSwapDeltaFits cf p.amountSpecified remaining calculated from fun hh => hb hh.2)]
      rw [if_neg hb] at hsecond
      exact ExecBlock.consNormal hfirst (ExecBlock.consRevert hsecond)
  · rw [if_neg (show ¬poolSwapDeltaFits cf p.amountSpecified remaining calculated from fun hh => ha hh.1)]
    rw [if_neg ha] at hfirst
    exact ExecBlock.consRevert hfirst

theorem poolSwapDeltaCondition_eval {f : Frame} {evm : State} {p : PoolSwapParamsWords}
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p))
    (hz : f.locals.get? "zeroForOne" = some (.bool p.zeroForOne)) :
    evalExpr? config f evm poolSwapDeltaCondition = .ok (.bool (poolSwapCalculatedFirst p.zeroForOne p.amountSpecified)) := by
  have hlt : evalExpr? config f evm (.binary .lt (.field (.var "params") "amountSpecified") (.intLit 0)) =
      .ok (.bool (decide (EVM.signed p.amountSpecified < 0))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalStructField (evalLocalValue hp) rfl]
    simp only [evalExpr?, pure, bind, EvalResult.bind, evalBinaryOp?]
  rw [poolSwapDeltaCondition, evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hz, hlt]
  simp only [bind, EvalResult.bind, evalBinaryOp?, poolSwapCalculatedFirst, BEq.beq, Value.bool.injEq, bne]

theorem poolSwapDeltaSource {f : Frame} {evm : State} {p : PoolSwapParamsWords} {remaining calculated : UInt256}
    {old : Value} (hf : f.contract = contract)
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p))
    (hr : f.locals.get? "amountSpecifiedRemaining" = some (.int (EVM.signed remaining)))
    (hc : f.locals.get? "amountCalculated" = some (.int (EVM.signed calculated)))
    (hz : f.locals.get? "zeroForOne" = some (.bool p.zeroForOne))
    (hd : f.locals.get? "swapDelta" = some old) :
    let cf := poolSwapCalculatedFirst p.zeroForOne p.amountSpecified
    ExecStmt config f evm poolSwapFunction.body[34]!
      (if poolSwapDeltaFits cf p.amountSpecified remaining calculated then
        .ok (poolSwapDeltaFrame f cf p.amountSpecified remaining calculated) evm else .reverted) := by
  have hg := poolSwapDeltaCondition_eval (evm := evm) hp hz
  have hb := poolSwapDeltaBranchSource (evm := evm) (poolSwapCalculatedFirst p.zeroForOne p.amountSpecified) hf hp hr hc hd
  rw [poolSwapFunction_delta]
  cases he : poolSwapCalculatedFirst p.zeroForOne p.amountSpecified
  · simp only [he] at hg hb ⊢
    exact ExecStmt.iteFalse hg hb
  · simp only [he] at hg hb ⊢
    exact ExecStmt.iteTrue hg hb

end Benchmarks.UniswapV4PoolManager

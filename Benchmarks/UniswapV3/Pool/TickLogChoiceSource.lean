import Benchmarks.UniswapV3.Pool.TickLogBoundsSource
import Benchmarks.UniswapV3.Pool.TickSqrtSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem evalTickLogBoundsEqual {frame : Frame} {evm : EVM.State} (log : UInt256)
    (hl : frame.locals.get? "tickLow" = some (.int (tickLogLow log)))
    (hh : frame.locals.get? "tickHi" = some (.int (tickLogHigh log))) :
    evalExpr? config frame evm (.binary .eq (.var "tickLow") (.var "tickHi")) =
      .ok (.bool (decide (tickLogLow log = tickLogHigh log))) := by
  have el := evalExpr_var_get (cfg := config) (evm := evm) hl
  have eh := evalExpr_var_get (cfg := config) (evm := evm) hh
  simp only [evalExpr?, el, eh, evalBinaryOp?, bind, EvalResult.bind]
  apply congrArg (fun b ↦ EvalResult.ok (Value.bool b))
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, Value.int.injEq]

def tickLogCalleeFrame (frame : Frame) (log : UInt256) : Frame :=
  resumeAfterInternalCall frame "__c0"
    (some [.int (Int.ofNat (tickSqrtValue (tickLogHigh log)).toNat)])

theorem tickLogCalleeSource {frame : Frame} {evm : EVM.State} (log : UInt256)
    (hc : frame.contract = contract)
    (hh : frame.locals.get? "tickHi" = some (.int (tickLogHigh log)))
    (hv : (tickLogHigh log).natAbs ≤ 887272) :
    ExecStmt config frame evm (.internalCall "TickMath_getSqrtRatioAtTick" [.var "tickHi"] "__c0")
      (.ok (tickLogCalleeFrame frame log) evm) := by
  obtain ⟨out, hbody⟩ := tickSqrtReturns frame.immutables evm (tickLogHigh log)
    (tickLogTick_bounds _).1 (tickLogTick_bounds _).2 hv
  have hf : {frame with locals := tickSqrtLocals (tickLogHigh log)} =
      tickSqrtFrame frame.immutables (tickLogHigh log) := by
    cases frame
    simp_all only [tickSqrtFrame]
  rw [← hf] at hbody
  apply internalCallFunctionReturn (callee := tickSqrtFunction) (calleeSolm := out)
    (argVals := [.int (tickLogHigh log)])
    (locals := tickSqrtLocals (tickLogHigh log)) (value := some
      [.int (Int.ofNat (tickSqrtValue (tickLogHigh log)).toNat)])
  · have eh := evalExpr_var_get (cfg := config) (evm := evm) hh
    simp only [evalExprs?, eh, bind, EvalResult.bind, pure]
  · simpa only [hc] using tickSqrtLookup
  · exact tickSqrtBind _
  · exact hbody

theorem tickLogCalleeSourceReverts {frame : Frame} {evm : EVM.State} (log : UInt256)
    (hc : frame.contract = contract)
    (hh : frame.locals.get? "tickHi" = some (.int (tickLogHigh log)))
    (hv : ¬ (tickLogHigh log).natAbs ≤ 887272) :
    ExecStmt config frame evm (.internalCall "TickMath_getSqrtRatioAtTick" [.var "tickHi"] "__c0")
      .reverted := by
  have hbody := tickSqrtReverts frame.immutables evm (tickLogHigh log)
    (tickLogTick_bounds _).1 (tickLogTick_bounds _).2 hv
  have hf : {frame with locals := tickSqrtLocals (tickLogHigh log)} =
      tickSqrtFrame frame.immutables (tickLogHigh log) := by
    cases frame
    simp_all only [tickSqrtFrame]
  rw [← hf] at hbody
  apply internalCallFunctionRevert (callee := tickSqrtFunction)
    (argVals := [.int (tickLogHigh log)])
    (locals := tickSqrtLocals (tickLogHigh log))
  · have eh := evalExpr_var_get (cfg := config) (evm := evm) hh
    simp only [evalExprs?, eh, bind, EvalResult.bind, pure]
  · simpa only [hc] using tickSqrtLookup
  · exact tickSqrtBind _
  · exact hbody

theorem evalTickLogChoice {frame : Frame} {evm : EVM.State} (log price : UInt256)
    (hl : frame.locals.get? "tickLow" = some (.int (tickLogLow log)))
    (hh : frame.locals.get? "tickHi" = some (.int (tickLogHigh log)))
    (hp : frame.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)))
    (hr : frame.locals.get? "__c0" =
      some (.int (Int.ofNat (tickSqrtValue (tickLogHigh log)).toNat))) :
    evalExpr? config frame evm
      (.ite (.binary .le (.var "__c0") (.var "sqrtPriceX96")) (.var "tickHi") (.var "tickLow")) =
      .ok (.int (if (tickSqrtValue (tickLogHigh log)).toNat ≤ price.toNat
        then tickLogHigh log else tickLogLow log)) := by
  have el := evalExpr_var_get (cfg := config) (evm := evm) hl
  have eh := evalExpr_var_get (cfg := config) (evm := evm) hh
  have ep := evalExpr_var_get (cfg := config) (evm := evm) hp
  have er := evalExpr_var_get (cfg := config) (evm := evm) hr
  have ecmp : evalExpr? config frame evm (.binary .le (.var "__c0") (.var "sqrtPriceX96")) =
      .ok (.bool (decide ((tickSqrtValue (tickLogHigh log)).toNat ≤ price.toNat))) := by
    simp only [evalExpr?, er, ep, evalBinaryOp?, bind, EvalResult.bind]
    apply congrArg (fun b ↦ EvalResult.ok (Value.bool b))
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact Int.ofNat_le
  by_cases h : (tickSqrtValue (tickLogHigh log)).toNat ≤ price.toNat
  · simp only [evalExpr?, ecmp, h, decide_true, bind, EvalResult.bind, eh, ↓reduceIte]
  · simp only [evalExpr?, ecmp, h, decide_false, bind, EvalResult.bind, el, ↓reduceIte]

theorem tickLogFinalSource {frame : Frame} {evm : EVM.State} (tick : Int)
    (hc : frame.locals.get? "__cond1" = some (.int tick))
    (ht : frame.locals.get? "tick" = some (.int 0)) :
    ∃ out, ExecBlock config frame evm (tickLogFunction.body.drop 75)
      (.returned out evm (some [.int tick])) := by
  let out : Frame := {frame with locals := frame.locals.insert "tick" (.int tick)}
  refine ⟨out, ExecBlock.consNormal (solm' := out) (evm' := evm)
    (ExecStmt.assign (evalExpr_var_get (cfg := config) (evm := evm) hc)
      (assignLocalVarBase_frame ht)) ?_⟩
  apply ExecBlock.consReturn
  apply ExecStmt.return
  have he : evalExpr? config out evm (.var "tick") = .ok (.int tick) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  simp only [evalExprs?, he, bind, EvalResult.bind, pure]

theorem tickLogChoiceSource {frame : Frame} {evm : EVM.State} (log price : UInt256)
    (hc : frame.contract = contract)
    (hl : frame.locals.get? "tickLow" = some (.int (tickLogLow log)))
    (hh : frame.locals.get? "tickHi" = some (.int (tickLogHigh log)))
    (hp : frame.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)))
    (hcond : frame.locals.get? "__cond1" = some (.int 0))
    (ht : frame.locals.get? "tick" = some (.int 0)) (hv : tickLogSafe log) :
    ∃ out, ExecBlock config frame evm (tickLogFunction.body.drop 74)
      (.returned out evm (some [.int (tickLogChoice log price)])) := by
  have heq := evalTickLogBoundsEqual (evm := evm) log hl hh
  by_cases he : tickLogLow log = tickLogHigh log
  · let chosen : Frame := {frame with locals := frame.locals.insert "__cond1" (.int (tickLogLow log))}
    obtain ⟨out, hr⟩ := tickLogFinalSource (frame := chosen) (evm := evm) (tickLogLow log)
      Std.HashMap.getElem?_insert_self (by
        change (frame.locals.insert "__cond1" (.int (tickLogLow log)))["tick"]? = _
        rw [Std.HashMap.getElem?_insert]
        exact ht)
    refine ⟨out, ?_⟩
    rw [tickLogChoice_eq, if_pos he]
    refine ExecBlock.consNormal (solm' := chosen) (evm' := evm) (ExecStmt.iteTrue ?_ ?_) hr
    · simpa only [he, decide_true] using heq
    · exact ExecBlock.consNormal (ExecStmt.assign (evalExpr_var_get (cfg := config) hl)
        (assignLocalVarBase_frame hcond)) ExecBlock.nil
  · have hv' : (tickLogHigh log).natAbs ≤ 887272 := hv.resolve_left he
    let mid := tickLogCalleeFrame frame log
    have hkeep (name : String) (hn : name ≠ "__c0") :
        mid.locals.get? name = frame.locals.get? name := by
      change (frame.locals.insert "__c0"
        (.int (Int.ofNat (tickSqrtValue (tickLogHigh log)).toNat)))[name]? = frame.locals[name]?
      simp only [Std.HashMap.getElem?_insert, beq_iff_eq, Ne.symm hn, if_false]
    have evalChoice := evalTickLogChoice (frame := mid) (evm := evm) log price
      (by rw [hkeep "tickLow" (by decide)]; exact hl)
      (by rw [hkeep "tickHi" (by decide)]; exact hh)
      (by rw [hkeep "sqrtPriceX96" (by decide)]; exact hp)
      Std.HashMap.getElem?_insert_self
    have hchoice := tickLogChoice_eq log price
    rw [if_neg he] at hchoice
    rw [← hchoice] at evalChoice
    let chosen : Frame :=
      {mid with locals := mid.locals.insert "__cond1" (.int (tickLogChoice log price))}
    obtain ⟨out, hr⟩ := tickLogFinalSource (frame := chosen) (evm := evm) (tickLogChoice log price)
      Std.HashMap.getElem?_insert_self (by
        change (mid.locals.insert "__cond1" (.int (tickLogChoice log price)))["tick"]? = _
        rw [Std.HashMap.getElem?_insert]
        exact (hkeep "tick" (by decide)).trans ht)
    refine ⟨out, ExecBlock.consNormal (solm' := chosen) (evm' := evm)
      (ExecStmt.iteFalse ?_ ?_) hr⟩
    · simpa only [he, decide_false] using heq
    · refine ExecBlock.consNormal (tickLogCalleeSource log hc hh hv') ?_
      exact ExecBlock.consNormal (ExecStmt.assign evalChoice (assignLocalVarBase_frame
        ((hkeep "__cond1" (by decide)).trans hcond))) ExecBlock.nil

theorem tickLogChoiceSourceReverts {frame : Frame} {evm : EVM.State} (log : UInt256)
    (hc : frame.contract = contract)
    (hl : frame.locals.get? "tickLow" = some (.int (tickLogLow log)))
    (hh : frame.locals.get? "tickHi" = some (.int (tickLogHigh log)))
    (hv : ¬ tickLogSafe log) :
    ExecBlock config frame evm (tickLogFunction.body.drop 74) .reverted := by
  have he : tickLogLow log ≠ tickLogHigh log := fun h ↦ hv (Or.inl h)
  have hs : ¬ (tickLogHigh log).natAbs ≤ 887272 := fun h ↦ hv (Or.inr h)
  refine ExecBlock.consRevert (ExecStmt.iteFalse ?_
    (ExecBlock.consRevert (tickLogCalleeSourceReverts log hc hh hs)))
  simpa only [he, decide_false] using evalTickLogBoundsEqual (evm := evm) log hl hh

end Benchmarks.UniswapV3.Pool

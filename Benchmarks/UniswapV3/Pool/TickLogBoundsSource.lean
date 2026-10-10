import Benchmarks.UniswapV3.Pool.TickLogBoundsModel
import Benchmarks.UniswapV3.Pool.SignedRightShift

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def tickLogScaledLogExpr : Expr :=
  .cast (.binary .mul (.var "log_2") (.intLit 255738958999603826347141))
    (.elem (.int (.sint ⟨256, by decide⟩)))

def tickLogLowExpr : Expr :=
  .cast (.binary (.shr (.sint ⟨256, by decide⟩))
    (.cast (.binary .sub (.var "log_sqrt10001") (.intLit 3402992956809132418596140100660247210))
      (.elem (.int (.sint ⟨256, by decide⟩)))) (.intLit 128))
    (.elem (.int (.sint ⟨24, by decide⟩)))

def tickLogHighExpr : Expr :=
  .cast (.binary (.shr (.sint ⟨256, by decide⟩))
    (.cast (.binary .add (.var "log_sqrt10001") (.intLit 291339464771989622907027621153398088495))
      (.elem (.int (.sint ⟨256, by decide⟩)))) (.intLit 128))
    (.elem (.int (.sint ⟨24, by decide⟩)))

theorem evalTickLogScaledLog {frame : Frame} {evm : EVM.State} (log : UInt256)
    (hl : frame.locals.get? "log_2" = some (.int (signedWordInt log))) :
    evalExpr? config frame evm tickLogScaledLogExpr = .ok (.int (signedWordInt (tickLogScaledLog log))) := by
  have he := evalExpr_sint_mul (evalExpr_var_get (cfg := config) (evm := evm) hl)
    (rhs := .intLit 255738958999603826347141) (j := 255738958999603826347141)
    (by simp only [evalExpr?, pure])
  simpa only [tickLogScaledLogExpr, tickLogScaledLog, wordOfInt_signedWordInt,
    show EVM.wordOfInt 255738958999603826347141 = UInt256.ofNat 255738958999603826347141 from rfl] using he

theorem evalTickLogLow {frame : Frame} {evm : EVM.State} (log : UInt256)
    (hl : frame.locals.get? "log_sqrt10001" = some (.int (signedWordInt (tickLogScaledLog log)))) :
    evalExpr? config frame evm tickLogLowExpr = .ok (.int (tickLogLow log)) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm) hl
  have hc : evalExpr? config frame evm
      (.cast (.binary .sub (.var "log_sqrt10001") (.intLit 3402992956809132418596140100660247210))
        (.elem (.int (.sint ⟨256, by decide⟩)))) =
      .ok (.int (normalizeInt (.sint ⟨256, by decide⟩)
        (signedWordInt (tickLogScaledLog log) - 3402992956809132418596140100660247210))) := by
    simp only [evalExpr?, he, evalBinaryOp?, castValue?, bind, EvalResult.bind, pure, EvalResult.ofOption]
  simpa only [tickLogLowExpr, tickLogLow, tickLogTick, tickLogLowRaw, wordOfInt_normalize256,
    wordOfInt_sub, wordOfInt_signedWordInt,
    show EVM.wordOfInt 3402992956809132418596140100660247210 =
      UInt256.ofNat 3402992956809132418596140100660247210 from rfl] using
    evalExpr_sint_sar_narrow ⟨24, by decide⟩ 128 (by decide) hc

theorem evalTickLogHigh {frame : Frame} {evm : EVM.State} (log : UInt256)
    (hl : frame.locals.get? "log_sqrt10001" = some (.int (signedWordInt (tickLogScaledLog log)))) :
    evalExpr? config frame evm tickLogHighExpr = .ok (.int (tickLogHigh log)) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm) hl
  have hc : evalExpr? config frame evm
      (.cast (.binary .add (.var "log_sqrt10001") (.intLit 291339464771989622907027621153398088495))
        (.elem (.int (.sint ⟨256, by decide⟩)))) =
      .ok (.int (normalizeInt (.sint ⟨256, by decide⟩)
        (signedWordInt (tickLogScaledLog log) + 291339464771989622907027621153398088495))) := by
    simp only [evalExpr?, he, evalBinaryOp?, castValue?, bind, EvalResult.bind, pure, EvalResult.ofOption]
  simpa only [tickLogHighExpr, tickLogHigh, tickLogTick, tickLogHighRaw, wordOfInt_normalize256,
    wordOfInt_add, wordOfInt_signedWordInt,
    show EVM.wordOfInt 291339464771989622907027621153398088495 =
      UInt256.ofNat 291339464771989622907027621153398088495 from rfl] using
    evalExpr_sint_sar_narrow ⟨24, by decide⟩ 128 (by decide) hc

def tickLogScaledFrame (frame : Frame) (log : UInt256) : Frame :=
  {frame with locals := frame.locals.insert "log_sqrt10001" (.int (signedWordInt (tickLogScaledLog log)))}

def tickLogLowFrame (frame : Frame) (log : UInt256) : Frame :=
  {tickLogScaledFrame frame log with
    locals := (tickLogScaledFrame frame log).locals.insert "tickLow" (.int (tickLogLow log))}

def tickLogHighFrame (frame : Frame) (log : UInt256) : Frame :=
  {tickLogLowFrame frame log with
    locals := (tickLogLowFrame frame log).locals.insert "tickHi" (.int (tickLogHigh log))}

def tickLogBoundsFrame (frame : Frame) (log : UInt256) : Frame :=
  {tickLogHighFrame frame log with
    locals := (tickLogHighFrame frame log).locals.insert "__cond1" (.int 0)}

theorem tickLogBoundsSource {frame : Frame} {evm : EVM.State} (log : UInt256)
    (hl : frame.locals.get? "log_2" = some (.int (signedWordInt log))) :
    ExecBlock config frame evm ((tickLogFunction.body.drop 70).take 4)
      (.ok (tickLogBoundsFrame frame log) evm) := by
  have hs : (tickLogScaledFrame frame log).locals.get? "log_sqrt10001" =
      some (.int (signedWordInt (tickLogScaledLog log))) := by
    change (tickLogScaledFrame frame log).locals["log_sqrt10001"]? = _
    exact Std.HashMap.getElem?_insert_self
  have hs' : (tickLogLowFrame frame log).locals.get? "log_sqrt10001" =
      some (.int (signedWordInt (tickLogScaledLog log))) := by
    change ((tickLogScaledFrame frame log).locals.insert "tickLow"
      (.int (tickLogLow log)))["log_sqrt10001"]? = _
    rw [Std.HashMap.getElem?_insert]
    exact hs
  refine ExecBlock.consNormal (solm' := tickLogScaledFrame frame log)
    (ExecStmt.letDecl (evalTickLogScaledLog log hl)) ?_
  refine ExecBlock.consNormal (solm' := tickLogLowFrame frame log)
    (ExecStmt.letDecl (evalTickLogLow log hs)) ?_
  refine ExecBlock.consNormal (solm' := tickLogHighFrame frame log)
    (ExecStmt.letDecl (evalTickLogHigh log hs')) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil

theorem tickLogBoundsFrame_values (frame : Frame) (log : UInt256) :
    (tickLogBoundsFrame frame log).locals.get? "tickLow" = some (.int (tickLogLow log)) ∧
      (tickLogBoundsFrame frame log).locals.get? "tickHi" = some (.int (tickLogHigh log)) ∧
      (tickLogBoundsFrame frame log).locals.get? "__cond1" = some (.int 0) := by
  simp only [tickLogBoundsFrame, tickLogHighFrame, tickLogLowFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert]
  exact ⟨rfl, rfl, rfl⟩

theorem tickLogBoundsFrame_preserves (frame : Frame) (log : UInt256) (name : String)
    (hn0 : name ≠ "log_sqrt10001") (hn1 : name ≠ "tickLow")
    (hn2 : name ≠ "tickHi") (hn3 : name ≠ "__cond1") :
    (tickLogBoundsFrame frame log).locals.get? name = frame.locals.get? name := by
  simp only [tickLogBoundsFrame, tickLogHighFrame, tickLogLowFrame, tickLogScaledFrame,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_iff_eq,
    Ne.symm hn0, Ne.symm hn1, Ne.symm hn2, Ne.symm hn3, if_false]

end Benchmarks.UniswapV3.Pool

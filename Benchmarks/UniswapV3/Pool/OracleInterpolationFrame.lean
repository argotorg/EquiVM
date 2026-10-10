import Benchmarks.UniswapV3.Pool.OracleInterpolationModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleInterpolationFrame (frame : Frame) (before after : OracleObservation)
    (target : UInt256) : Frame :=
  { frame with
    locals := (frame.locals.insert "observationTimeDelta"
      (.int (Int.ofNat (oracleDelta after.timestamp before.timestamp).toNat))).insert "targetDelta"
      (.int (Int.ofNat (oracleDelta target before.timestamp).toNat)) }

theorem oracleInterpolationPrefix {frame : Frame} {evm : EVM.State}
    (before after : OracleObservation) (target : UInt256)
    (ht : frame.locals.get? "target" = some (.int (Int.ofNat target.toNat)))
    (hb : frame.locals.get? "beforeOrAt" = some before.value)
    (ha : frame.locals.get? "atOrAfter" = some after.value) :
    ExecBlock config frame evm (oracleInterpolationBlock.take 2)
      (.ok (oracleInterpolationFrame frame before after target) evm) := by
  have hd := evalOracleDelta (evm := evm) (evalOracleTimestamp after ha) (evalOracleTimestamp before hb)
  let f1 : Frame := { frame with
    locals := frame.locals.insert "observationTimeDelta"
      (.int (Int.ofNat (oracleDelta after.timestamp before.timestamp).toNat)) }
  have ht1 : f1.locals.get? "target" = some (.int (Int.ofNat target.toNat)) := by
    simpa [f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using ht
  have hb1 : f1.locals.get? "beforeOrAt" = some before.value := by
    simpa [f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hb
  refine ExecBlock.consNormal (ExecStmt.letDecl hd) ?_
  change ExecBlock config f1 evm [oracleInterpolationBlock[1]!]
    (.ok (oracleInterpolationFrame frame before after target) evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl (value :=
    .int (Int.ofNat (oracleDelta target before.timestamp).toNat)) ?_) ExecBlock.nil
  exact evalOracleDelta (evalExpr_var_get ht1) (evalOracleTimestamp before hb1)

theorem oracleInterpolationGets {frame : Frame} (before after : OracleObservation) (target : UInt256)
    (hb : frame.locals.get? "beforeOrAt" = some before.value)
    (ha : frame.locals.get? "atOrAfter" = some after.value) :
    let f := oracleInterpolationFrame frame before after target
    f.locals.get? "beforeOrAt" = some before.value ∧
      f.locals.get? "atOrAfter" = some after.value ∧
      f.locals.get? "observationTimeDelta" =
        some (.int (Int.ofNat (oracleDelta after.timestamp before.timestamp).toNat)) ∧
      f.locals.get? "targetDelta" =
        some (.int (Int.ofNat (oracleDelta target before.timestamp).toNat)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [oracleInterpolationFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hb
  · simpa [oracleInterpolationFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using ha
  · simp [oracleInterpolationFrame, Std.HashMap.getElem_insert]
  · simp [oracleInterpolationFrame]

theorem oracleObserveInterpolationBranchStep {frame : Frame} {evm : EVM.State} {result : ExecResult}
    (target : UInt256) (before after : OracleObservation)
    (ht : frame.locals.get? "target" = some (.int (Int.ofNat target.toNat)))
    (hb : frame.locals.get? "beforeOrAt" = some before.value)
    (ha : frame.locals.get? "atOrAfter" = some after.value)
    (hnb : target ≠ before.timestamp) (hna : target ≠ after.timestamp)
    (hbody : ExecBlock config frame evm oracleInterpolationBlock result) :
    ExecStmt config frame evm oracleObserveSingleFunction.body[7]! result := by
  rw [oracleInterpolationBranch]
  refine ExecStmt.iteFalse ?_ (execBlock_singleton ?_)
  · have h := evalExpr_word_eq (evalExpr_var_get (cfg := config) (evm := evm) ht)
      (evalOracleTimestamp before hb)
    simpa only [hnb, decide_false] using h
  refine ExecStmt.iteFalse ?_ hbody
  have h := evalExpr_word_eq (evalExpr_var_get (cfg := config) (evm := evm) ht)
    (evalOracleTimestamp after ha)
  simpa only [hna, decide_false] using h

end Benchmarks.UniswapV3.Pool

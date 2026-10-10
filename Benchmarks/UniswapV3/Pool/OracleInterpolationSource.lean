import Benchmarks.UniswapV3.Pool.OracleInterpolationEval
import Benchmarks.UniswapV3.Pool.OracleInterpolationFrame

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleInterpolationReturns {frame : Frame} {evm : EVM.State}
    (before after : OracleObservation) (target : UInt256)
    (ht : frame.locals.get? "target" = some (.int (Int.ofNat target.toNat)))
    (hb : frame.locals.get? "beforeOrAt" = some before.value)
    (ha : frame.locals.get? "atOrAfter" = some after.value)
    (hn : (oracleDelta after.timestamp before.timestamp).toNat ≠ 0) :
    ExecBlock config frame evm oracleInterpolationBlock
      (.returned (oracleInterpolationFrame frame before after target) evm
        (some (oracleInterpolatedValues before after target))) := by
  rw [← List.take_append_drop 2 oracleInterpolationBlock]
  apply execBlock_append_ok (oracleInterpolationPrefix before after target ht hb ha)
  refine ExecBlock.consReturn (ExecStmt.return ?_)
  obtain ⟨hb', ha', hd', ht'⟩ := oracleInterpolationGets before after target hb ha
  have et := evalOracleInterpolationTick (evm := evm) before after target hb' ha' hd' ht' hn
  have es := evalOracleInterpolationSeconds (evm := evm) before after target hb' ha' hd' ht' hn
  change evalExprs? _ _ _ [oracleInterpolationTickExpr, oracleInterpolationSecondsExpr] = _
  simp only [evalExprs?, et, es, bind, EvalResult.bind, pure]
  rfl

theorem oracleInterpolationReverts {frame : Frame} {evm : EVM.State}
    (before after : OracleObservation) (target : UInt256)
    (ht : frame.locals.get? "target" = some (.int (Int.ofNat target.toNat)))
    (hb : frame.locals.get? "beforeOrAt" = some before.value)
    (ha : frame.locals.get? "atOrAfter" = some after.value)
    (hz : (oracleDelta after.timestamp before.timestamp).toNat = 0) :
    ExecBlock config frame evm oracleInterpolationBlock .reverted := by
  rw [← List.take_append_drop 2 oracleInterpolationBlock]
  apply execBlock_append_ok (oracleInterpolationPrefix before after target ht hb ha)
  refine ExecBlock.consRevert (ExecStmt.returnRevert ?_)
  obtain ⟨hb', ha', hd', _⟩ := oracleInterpolationGets before after target hb ha
  have hd0 : (oracleInterpolationFrame frame before after target).locals.get?
      "observationTimeDelta" = some (.int 0) := by simpa only [hz] using hd'
  have et := evalOracleInterpolationZero (evm := evm) before after hb' ha' hd0
  change evalExprs? _ _ _ [oracleInterpolationTickExpr, oracleInterpolationSecondsExpr] = .revert
  simp only [evalExprs?, et, bind, EvalResult.bind]

end Benchmarks.UniswapV3.Pool

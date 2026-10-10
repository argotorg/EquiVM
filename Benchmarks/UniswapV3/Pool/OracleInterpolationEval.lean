import Benchmarks.UniswapV3.Pool.OracleInterpolationModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem evalOracleInterpolationTick {frame : Frame} {evm : EVM.State}
    (before after : OracleObservation) (target : UInt256)
    (hb : frame.locals.get? "beforeOrAt" = some before.value)
    (ha : frame.locals.get? "atOrAfter" = some after.value)
    (hd : frame.locals.get? "observationTimeDelta" =
      some (.int (Int.ofNat (oracleDelta after.timestamp before.timestamp).toNat)))
    (ht : frame.locals.get? "targetDelta" =
      some (.int (Int.ofNat (oracleDelta target before.timestamp).toNat)))
    (hn : (oracleDelta after.timestamp before.timestamp).toNat ≠ 0) :
    evalExpr? config frame evm oracleInterpolationTickExpr =
      .ok (.int (oracleInterpolatedTick before after target)) := by
  have eb := evalExpr_var_get (cfg := config) (evm := evm) hb
  have ea := evalExpr_var_get (cfg := config) (evm := evm) ha
  have ed := evalExpr_var_get (cfg := config) (evm := evm) hd
  have et := evalExpr_var_get (cfg := config) (evm := evm) ht
  simp [oracleInterpolationTickExpr, oracleInterpolatedTick, evalExpr?, eb, ea, ed, et,
    OracleObservation.value, lookupField?, lookupAssoc, EvalResult.ofOption,
    bind, EvalResult.bind, castValue?, evalBinaryOp?, hn]

theorem evalOracleInterpolationSeconds {frame : Frame} {evm : EVM.State}
    (before after : OracleObservation) (target : UInt256)
    (hb : frame.locals.get? "beforeOrAt" = some before.value)
    (ha : frame.locals.get? "atOrAfter" = some after.value)
    (hd : frame.locals.get? "observationTimeDelta" =
      some (.int (Int.ofNat (oracleDelta after.timestamp before.timestamp).toNat)))
    (ht : frame.locals.get? "targetDelta" =
      some (.int (Int.ofNat (oracleDelta target before.timestamp).toNat)))
    (hn : (oracleDelta after.timestamp before.timestamp).toNat ≠ 0) :
    evalExpr? config frame evm oracleInterpolationSecondsExpr =
      .ok (.int (oracleInterpolatedSeconds before after target)) := by
  have eb := evalExpr_var_get (cfg := config) (evm := evm) hb
  have ea := evalExpr_var_get (cfg := config) (evm := evm) ha
  have ed := evalExpr_var_get (cfg := config) (evm := evm) hd
  have et := evalExpr_var_get (cfg := config) (evm := evm) ht
  simp [oracleInterpolationSecondsExpr, oracleInterpolatedSeconds, evalExpr?, eb, ea, ed, et,
    OracleObservation.value, lookupField?, lookupAssoc, EvalResult.ofOption,
    bind, EvalResult.bind, castValue?, evalBinaryOp?, hn]

theorem evalOracleInterpolationZero {frame : Frame} {evm : EVM.State}
    (before after : OracleObservation)
    (hb : frame.locals.get? "beforeOrAt" = some before.value)
    (ha : frame.locals.get? "atOrAfter" = some after.value)
    (hd : frame.locals.get? "observationTimeDelta" = some (.int 0)) :
    evalExpr? config frame evm oracleInterpolationTickExpr = .revert := by
  have eb := evalExpr_var_get (cfg := config) (evm := evm) hb
  have ea := evalExpr_var_get (cfg := config) (evm := evm) ha
  have ed := evalExpr_var_get (cfg := config) (evm := evm) hd
  simp [oracleInterpolationTickExpr, evalExpr?, eb, ea, ed,
    OracleObservation.value, lookupField?, lookupAssoc, EvalResult.ofOption,
    bind, EvalResult.bind, castValue?, evalBinaryOp?]

end Benchmarks.UniswapV3.Pool

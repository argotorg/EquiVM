import Benchmarks.UniswapV3.Pool.SwapCrossFlags
import Benchmarks.UniswapV3.Pool.SourceTuples

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapObservationArgs : List Expr :=
  [.field (.var "cache") "blockTimestamp", .intLit 0, .field (.var "slot0Start") "tick",
    .field (.var "slot0Start") "observationIndex", .field (.var "cache") "liquidityStart",
    .field (.var "slot0Start") "observationCardinality"]

theorem swapObservationCallStmt : swapObservationBody[0]! =
    .internalCall "Oracle_observeSingle" swapObservationArgs "__c12" := rfl

theorem evalSwapObservationArgs {frame : Frame} {evm : EVM.State}
    (c : SwapCacheData) (initial : EVM.State)
    (hc : frame.locals.get? "cache" = some c.value)
    (hs : frame.locals.get? "slot0Start" =
      some (slot0StructValue initial.accountMap initial.executionEnv)) :
    evalExprs? config frame evm swapObservationArgs = .ok
      [.int (Int.ofNat c.blockTimestamp.toNat), .int 0,
        .int (slot0TickValue initial.accountMap initial.executionEnv),
        .int (Int.ofNat (slot0FieldWord 23 2 initial.accountMap initial.executionEnv).toNat),
        .int (Int.ofNat c.liquidityStart.toNat),
        .int (Int.ofNat (slot0FieldWord 25 2 initial.accountMap initial.executionEnv).toNat)] := by
  have ec := evalExpr_var_get (cfg := config) (evm := evm) hc
  have es := evalExpr_var_get (cfg := config) (evm := evm) hs
  have htime := evalExpr_structField (name := "blockTimestamp") ec rfl
  have hliq := evalExpr_structField (name := "liquidityStart") ec rfl
  have htick := evalExpr_structField (name := "tick") es rfl
  have hindex := evalExpr_structField (name := "observationIndex") es rfl
  have hcard := evalExpr_structField (name := "observationCardinality") es rfl
  simp only [swapObservationArgs, evalExprs?, htime, hliq, htick, hindex, hcard,
    bind, EvalResult.bind, evalExpr?, pure]

def swapCacheFrame (frame : Frame) (c : SwapCacheData) : Frame :=
  {frame with locals := frame.locals.insert "cache" c.value}

def swapObservationCache (c : SwapCacheData) (tick : Int) (seconds : UInt256) : SwapCacheData :=
  {c with
    tickCumulative := tick
    secondsPerLiquidity := seconds
    computedLatestObservation := true}

def swapObservationCallFrame (frame : Frame) (tick : Int) (seconds : UInt256) : Frame :=
  resumeAfterInternalCall frame "__c12" (some [.int tick, .int (Int.ofNat seconds.toNat)])

def swapObservationTickFrame (frame : Frame) (c : SwapCacheData) (tick : Int)
    (seconds : UInt256) : Frame :=
  swapCacheFrame (swapObservationCallFrame frame tick seconds) {c with tickCumulative := tick}

def swapObservationSecondsFrame (frame : Frame) (c : SwapCacheData) (tick : Int)
    (seconds : UInt256) : Frame :=
  swapCacheFrame (swapObservationTickFrame frame c tick seconds)
    {c with tickCumulative := tick, secondsPerLiquidity := seconds}

def swapObservationFrame (frame : Frame) (c : SwapCacheData) (tick : Int)
    (seconds : UInt256) : Frame :=
  swapCacheFrame (swapObservationSecondsFrame frame c tick seconds)
    (swapObservationCache c tick seconds)

theorem swapObservationStoresSource {frame : Frame} {evm : EVM.State}
    (c : SwapCacheData) (tick : Int) (seconds : UInt256)
    (hc : frame.locals.get? "cache" = some c.value) :
    ExecBlock config (swapObservationCallFrame frame tick seconds) evm
      (swapObservationBody.drop 1) (.ok (swapObservationFrame frame c tick seconds) evm) := by
  have hc0 := (resumeAfterInternalCall_get frame "__c12" "cache"
    (some [.int tick, .int (Int.ofNat seconds.toNat)]) (by decide)).trans hc
  have hr : (swapObservationCallFrame frame tick seconds).locals.get? "__c12" =
      some (.tuple [.int tick, .int (Int.ofNat seconds.toNat)]) :=
    Std.HashMap.getElem?_insert_self
  have h1 : ExecStmt config (swapObservationCallFrame frame tick seconds) evm
      swapObservationBody[1]! (.ok (swapObservationTickFrame frame c tick seconds) evm) :=
    ExecStmt.assign (evalExpr_tupleGet (evalExpr_var_get hr) rfl)
      (assignLocalField_frame hc0 rfl rfl)
  have hr1 : (swapObservationTickFrame frame c tick seconds).locals.get? "__c12" =
      some (.tuple [.int tick, .int (Int.ofNat seconds.toNat)]) := by
    simpa only [swapObservationTickFrame, swapCacheFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hr
  have h2 : ExecStmt config (swapObservationTickFrame frame c tick seconds) evm
      swapObservationBody[2]! (.ok (swapObservationSecondsFrame frame c tick seconds) evm) :=
    ExecStmt.assign (evalExpr_tupleGet (evalExpr_var_get hr1) rfl)
      (assignLocalField_frame Std.HashMap.getElem?_insert_self rfl rfl)
  have h3 : ExecStmt config (swapObservationSecondsFrame frame c tick seconds) evm
      swapObservationBody[3]! (.ok (swapObservationFrame frame c tick seconds) evm) :=
    ExecStmt.assign (by simp only [evalExpr?, pure]; rfl)
      (assignLocalField_frame Std.HashMap.getElem?_insert_self rfl rfl)
  exact ExecBlock.consNormal h1 (ExecBlock.consNormal h2 (ExecBlock.consNormal h3 .nil))

theorem swapObservationCache_fits (c : SwapCacheData) (tick : Int) (seconds : UInt256)
    (hc : c.Fits) (ht : -(2 ^ 55 : Int) ≤ tick ∧ tick < 2 ^ 55)
    (hs : seconds.toNat < 2 ^ 160) : (swapObservationCache c tick seconds).Fits :=
  ⟨hc.1, hc.2.1, hc.2.2.1, ht, hs⟩

end Benchmarks.UniswapV3.Pool

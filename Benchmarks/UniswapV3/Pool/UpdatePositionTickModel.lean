import Benchmarks.UniswapV3.Pool.UpdatePositionObserve
import Benchmarks.UniswapV3.Pool.TickUpdateSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def updatePositionTickArgs (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : TickUpdateArgs :=
  {tick := if upper then a.upper else a.lower, current := a.current, delta := a.delta,
    global0 := feeGrowthWord false evm.accountMap evm.executionEnv,
    global1 := feeGrowthWord true evm.accountMap evm.executionEnv,
    secondsPerLiquidity := (snapshotCurrent evm.accountMap evm.executionEnv).secondsPerLiquidity,
    cumulative := (snapshotCurrent evm.accountMap evm.executionEnv).tickCumulative,
    time := blockTimestampWord evm.executionEnv, upper := upper,
    maxLiquidity := uint128Word v.maxLiquidityPerTick}

theorem updatePositionTickArgs_fits (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) (ha : a.Fits) : (updatePositionTickArgs v a evm upper).Fits := by
  have ho := snapshotCurrent_valid evm.accountMap evm.executionEnv
  refine ⟨?_, ha.2.2.2, ha.2.2.1, ho.seconds, ho.tick,
    blockTimestampWord_lt _, uint128Word_lt _⟩
  cases upper
  · exact ha.1
  · exact ha.2.1

def updatePositionLowerState (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : EVM.State := tickUpdateFinalState (updatePositionTickArgs v a evm false) evm

def updatePositionTickBefore (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : EVM.State :=
  if upper then updatePositionLowerState v a evm else evm

def updatePositionTickAfter (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : EVM.State :=
  tickUpdateFinalState (updatePositionTickArgs v a evm upper) (updatePositionTickBefore v a evm upper)

def updatePositionFlipped (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : Bool :=
  tickUpdateFlipped (updatePositionTickArgs v a evm upper) (updatePositionTickBefore v a evm upper)

def updatePositionLowerCallFrame (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : Frame :=
  let frame := updatePositionOracleFrame (immStore v) a evm
  {frame with locals := frame.locals.insert "__c3" (.bool (updatePositionFlipped v a evm false))}

def updatePositionLowerFrame (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : Frame :=
  let frame := updatePositionLowerCallFrame v a evm
  {frame with locals := frame.locals.insert "flippedLower" (.bool (updatePositionFlipped v a evm false))}

def updatePositionUpperCallFrame (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : Frame :=
  let frame := updatePositionLowerFrame v a evm
  {frame with locals := frame.locals.insert "__c4" (.bool (updatePositionFlipped v a evm true))}

def updatePositionUpperFrame (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : Frame :=
  let frame := updatePositionUpperCallFrame v a evm
  {frame with locals := frame.locals.insert "flippedUpper" (.bool (updatePositionFlipped v a evm true))}

def updatePositionTickInputFrame (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : Frame :=
  if upper then updatePositionLowerFrame v a evm else updatePositionOracleFrame (immStore v) a evm

def updatePositionTickCallFrame (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : Frame :=
  if upper then updatePositionUpperCallFrame v a evm else updatePositionLowerCallFrame v a evm

def updatePositionTickDoneFrame (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : Frame :=
  if upper then updatePositionUpperFrame v a evm else updatePositionLowerFrame v a evm

def updatePositionTickExprs (upper : Bool) : List Expr :=
  [.var (if upper then "tickUpper" else "tickLower"), .var "tick", .var "liquidityDelta",
    .var "_feeGrowthGlobal0X128", .var "_feeGrowthGlobal1X128",
    .var "secondsPerLiquidityCumulativeX128", .var "tickCumulative", .var "time", .boolLit upper,
    .cast (.immutable "maxLiquidityPerTick") (.elem (.int (.uint ⟨128, by decide⟩)))]

macro "update_position_tick_get" : tactic =>
  `(tactic| (simp only [updatePositionTickDoneFrame, updatePositionTickCallFrame,
    updatePositionTickInputFrame, updatePositionUpperFrame, updatePositionUpperCallFrame,
    updatePositionLowerFrame, updatePositionLowerCallFrame, updatePositionOracleFrame,
    updatePositionCumulativeFrame, updatePositionObservedFrame, updatePositionTimeFrame,
    Bool.false_eq_true, if_false, if_true,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; update_position_prefix_get))

theorem evalMaxLiquidityPerTick128 (v : UniswapV3PoolImmutables) (locals : Store)
    (evm : EVM.State) :
    evalExpr? config {contract := contract, locals := locals, immutables := immStore v} evm
      (.cast (.immutable "maxLiquidityPerTick") (.elem (.int (.uint ⟨128, by decide⟩)))) =
      .ok (.int (Int.ofNat (uint128Word v.maxLiquidityPerTick).toNat)) := by
  have h := evalExpr_intCast (.uint ⟨128, by decide⟩)
    (evalImmutable_maxLiquidityPerTick config contract locals evm v)
  rw [normalizeUIntWord_mask ⟨128, by decide⟩ v.maxLiquidityPerTick
    (UInt256.ofNat (2 ^ 128 - 1)) (by decide)] at h
  simpa only [uint128Word, u256_land_comm] using h

end Benchmarks.UniswapV3.Pool

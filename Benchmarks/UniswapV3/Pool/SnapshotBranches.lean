import Benchmarks.UniswapV3.Pool.SnapshotReady
import Benchmarks.UniswapV3.Pool.OracleObserveSource
import Benchmarks.UniswapV3.Pool.BlockTimestamp
import Benchmarks.UniswapV3.Pool.PoolLiquidityStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

structure SnapshotCumulatives where
  tick : Int
  secondsPerLiquidity : Int
  seconds : Int

def SnapshotCumulatives.values (result : SnapshotCumulatives) : List Value :=
  [.int result.tick, .int result.secondsPerLiquidity, .int result.seconds]

def snapshotDifference (a b : TickOutside) : SnapshotCumulatives :=
  ⟨normalizeInt (.sint ⟨56, by decide⟩) (a.cumulative - b.cumulative),
   normalizeInt (.uint ⟨160, by decide⟩)
     (Int.ofNat a.secondsPerLiquidity.toNat - Int.ofNat b.secondsPerLiquidity.toNat),
   normalizeInt (.uint ⟨32, by decide⟩) (Int.ofNat a.seconds.toNat - Int.ofNat b.seconds.toNat)⟩

def snapshotInside (current : OracleObservation) (time : UInt256) (a b : TickOutside) : SnapshotCumulatives :=
  ⟨normalizeInt (.sint ⟨56, by decide⟩)
     (normalizeInt (.sint ⟨56, by decide⟩) (current.tickCumulative - a.cumulative) - b.cumulative),
   normalizeInt (.uint ⟨160, by decide⟩)
     (normalizeInt (.uint ⟨160, by decide⟩)
       (Int.ofNat current.secondsPerLiquidity.toNat - Int.ofNat a.secondsPerLiquidity.toNat) -
       Int.ofNat b.secondsPerLiquidity.toNat),
   normalizeInt (.uint ⟨32, by decide⟩)
     (normalizeInt (.uint ⟨32, by decide⟩) (Int.ofNat time.toNat - Int.ofNat a.seconds.toNat) -
       Int.ofNat b.seconds.toNat)⟩

def snapshotCurrent (σ : AccountMap) (I : ExecutionEnv) : OracleObservation :=
  oracleObserveZeroResult (oracleStoredObservation (slot0FieldWord 23 2 σ I) σ I)
    (blockTimestampWord I) (slot0TickValue σ I) (poolLiquidityWord σ I)
def snapshotResult (lower upper : Int) (σ : AccountMap) (I : ExecutionEnv) : SnapshotCumulatives :=
  if slot0TickValue σ I < lower then snapshotDifference (tickOutside lower σ I) (tickOutside upper σ I)
  else if slot0TickValue σ I < upper then
    snapshotInside (snapshotCurrent σ I) (blockTimestampWord I) (tickOutside lower σ I) (tickOutside upper σ I)
  else snapshotDifference (tickOutside upper σ I) (tickOutside lower σ I)

def snapshotBelowBody : List Stmt :=
  [.return [
    .cast (.binary .sub (.var "tickCumulativeLower") (.var "tickCumulativeUpper"))
      (.elem (.int (.sint ⟨56, by decide⟩))),
    .cast (.binary .sub (.var "secondsPerLiquidityOutsideLowerX128")
      (.var "secondsPerLiquidityOutsideUpperX128")) (.elem (.int (.uint ⟨160, by decide⟩))),
    .cast (.binary .sub (.var "secondsOutsideLower") (.var "secondsOutsideUpper"))
      (.elem (.int (.uint ⟨32, by decide⟩)))]]
def snapshotAboveBody : List Stmt :=
  [.return [
    .cast (.binary .sub (.var "tickCumulativeUpper") (.var "tickCumulativeLower"))
      (.elem (.int (.sint ⟨56, by decide⟩))),
    .cast (.binary .sub (.var "secondsPerLiquidityOutsideUpperX128")
      (.var "secondsPerLiquidityOutsideLowerX128")) (.elem (.int (.uint ⟨160, by decide⟩))),
    .cast (.binary .sub (.var "secondsOutsideUpper") (.var "secondsOutsideLower"))
      (.elem (.int (.uint ⟨32, by decide⟩)))]]

theorem evalSnapshotLower (v : UniswapV3PoolImmutables) (evm : EVM.State) (lower upper : Int) :
    evalExpr? config (snapshotReadyFrame v lower upper evm.accountMap evm.executionEnv) evm
      (.binary .lt (.field (.var "_slot0") "tick") (.var "tickLower")) =
      .ok (.bool (decide (slot0TickValue evm.accountMap evm.executionEnv < lower))) := by
  simp [evalExpr?, snapshotReadyFrame, snapshotBothFrame, snapshotUpperReadFrame,
    snapshotLowerFrame, snapshotLowerReadFrame, snapshotAliasesFrame, snapshotLowerAliasFrame,
    snapshotZerosFrame, snapshotCheckedFrame, snapshotDelegateFrame, snapshotInitialFrame,
    snapshotLocals, checkTicksLocals, Std.HashMap.getElem_insert, slot0StructValue,
    lookupField?, lookupAssoc, EvalResult.ofOption, evalBinaryOp?, bind, EvalResult.bind]

theorem evalSnapshotUpper (v : UniswapV3PoolImmutables) (evm : EVM.State) (lower upper : Int) :
    evalExpr? config (snapshotReadyFrame v lower upper evm.accountMap evm.executionEnv) evm
      (.binary .lt (.field (.var "_slot0") "tick") (.var "tickUpper")) =
      .ok (.bool (decide (slot0TickValue evm.accountMap evm.executionEnv < upper))) := by
  simp [evalExpr?, snapshotReadyFrame, snapshotBothFrame, snapshotUpperReadFrame,
    snapshotLowerFrame, snapshotLowerReadFrame, snapshotAliasesFrame, snapshotLowerAliasFrame,
    snapshotZerosFrame, snapshotCheckedFrame, snapshotDelegateFrame, snapshotInitialFrame,
    snapshotLocals, checkTicksLocals, Std.HashMap.getElem_insert, slot0StructValue,
    lookupField?, lookupAssoc, EvalResult.ofOption, evalBinaryOp?, bind, EvalResult.bind]

theorem snapshotBelowReturns (v : UniswapV3PoolImmutables) (evm : EVM.State) (lower upper : Int) :
    let frame := snapshotReadyFrame v lower upper evm.accountMap evm.executionEnv
    ExecBlock config frame evm snapshotBelowBody (.returned frame evm
      (some (snapshotDifference (tickOutside lower evm.accountMap evm.executionEnv)
        (tickOutside upper evm.accountMap evm.executionEnv)).values)) := by
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp [evalExprs?, evalExpr?, snapshotReadyFrame, snapshotBothFrame,
    snapshotUpperReadFrame, snapshotLowerFrame, snapshotLowerReadFrame, Std.HashMap.getElem_insert,
    EvalResult.ofOption, bind, EvalResult.bind, pure, castValue?, evalBinaryOp?,
    snapshotDifference, SnapshotCumulatives.values]

theorem snapshotAboveReturns (v : UniswapV3PoolImmutables) (evm : EVM.State) (lower upper : Int) :
    let frame := snapshotReadyFrame v lower upper evm.accountMap evm.executionEnv
    ExecBlock config frame evm snapshotAboveBody (.returned frame evm
      (some (snapshotDifference (tickOutside upper evm.accountMap evm.executionEnv)
        (tickOutside lower evm.accountMap evm.executionEnv)).values)) := by
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp [evalExprs?, evalExpr?, snapshotReadyFrame, snapshotBothFrame,
    snapshotUpperReadFrame, snapshotLowerFrame, snapshotLowerReadFrame, Std.HashMap.getElem_insert,
    EvalResult.ofOption, bind, EvalResult.bind, pure, castValue?, evalBinaryOp?,
    snapshotDifference, SnapshotCumulatives.values]

end Benchmarks.UniswapV3.Pool

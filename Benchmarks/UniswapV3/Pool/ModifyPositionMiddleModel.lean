import Benchmarks.UniswapV3.Pool.ModifyPositionUpdateSource
import Benchmarks.UniswapV3.Pool.OracleWriteResult
import Benchmarks.UniswapV3.Pool.PoolLiquidityStorage
import Benchmarks.UniswapV3.Pool.BlockTimestamp

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def modifyPositionMiddleLiquidity (v : UniswapV3PoolImmutables) (a : ModifyPositionArgs)
    (evm : EVM.State) : UInt256 :=
  let updated := modifyPositionUpdatedState v a evm
  poolLiquidityWord updated.accountMap updated.executionEnv

def modifyPositionMiddleOracleArgs (v : UniswapV3PoolImmutables) (a : ModifyPositionArgs)
    (evm : EVM.State) : OracleWriteArgs :=
  {index := slot0FieldWord 23 2 evm.accountMap evm.executionEnv,
    time := blockTimestampWord (modifyPositionUpdatedState v a evm).executionEnv,
    tick := slot0TickValue evm.accountMap evm.executionEnv,
    liquidity := modifyPositionMiddleLiquidity v a evm,
    cardinality := slot0FieldWord 25 2 evm.accountMap evm.executionEnv,
    cardinalityNext := slot0FieldWord 27 2 evm.accountMap evm.executionEnv}

def modifyPositionMiddleLiquidityFrame (v : UniswapV3PoolImmutables) (a : ModifyPositionArgs)
    (evm : EVM.State) : Frame :=
  let frame := modifyPositionUpdatedFrame (immStore v) a evm
  let locals := frame.locals.insert "liquidityBefore"
    (.int (Int.ofNat (modifyPositionMiddleLiquidity v a evm).toNat))
  {frame with locals := locals}

def modifyPositionMiddleTimeFrame (v : UniswapV3PoolImmutables) (a : ModifyPositionArgs)
    (evm : EVM.State) : Frame :=
  resumeAfterInternalCall (modifyPositionMiddleLiquidityFrame v a evm) "__c6"
    (some [.int (Int.ofNat (modifyPositionMiddleOracleArgs v a evm).time.toNat)])

def modifyPositionMiddleOracleFrame (v : UniswapV3PoolImmutables) (a : ModifyPositionArgs)
    (evm : EVM.State) : Frame :=
  let args := modifyPositionMiddleOracleArgs v a evm
  let updated := modifyPositionUpdatedState v a evm
  resumeAfterInternalCall (modifyPositionMiddleTimeFrame v a evm) "__c7"
    (some [.int (Int.ofNat (oracleWriteResultIndex args updated).toNat),
      .int (Int.ofNat (oracleWriteResultCardinality args updated).toNat)])

def modifyPositionMiddleOracleState (v : UniswapV3PoolImmutables) (a : ModifyPositionArgs)
    (evm : EVM.State) : EVM.State :=
  oracleWriteState (modifyPositionMiddleOracleArgs v a evm) (modifyPositionUpdatedState v a evm)

def modifyPositionMiddleOracleExprs : List Expr :=
  [.field (.var "_slot0") "observationIndex", .var "__c6", .field (.var "_slot0") "tick",
    .var "liquidityBefore", .field (.var "_slot0") "observationCardinality",
    .field (.var "_slot0") "observationCardinalityNext"]

def modifyPositionMiddleBody : List Stmt :=
  [.letDecl "liquidityBefore" (some (.elem (.int (.uint ⟨128, by decide⟩))))
      (.storage ⟨"liquidity", []⟩),
    .internalCall "_blockTimestamp" [] "__c6",
    .internalCall "Oracle_write" modifyPositionMiddleOracleExprs "__c7",
    .assign .storage ⟨"slot0", [.field "observationIndex"]⟩ (.tupleGet (.var "__c7") 0),
    .assign .storage ⟨"slot0", [.field "observationCardinality"]⟩ (.tupleGet (.var "__c7") 1),
    .internalCall "TickMath_getSqrtRatioAtTick" [.field (.var "params") "tickUpper"] "__c8",
    .internalCall "SqrtPriceMath_getAmount0Delta"
      [.field (.var "_slot0") "sqrtPriceX96", .var "__c8", .field (.var "params") "liquidityDelta"]
      "__c9",
    .assign .localVar ⟨"amount0", []⟩ (.var "__c9"),
    .internalCall "TickMath_getSqrtRatioAtTick" [.field (.var "params") "tickLower"] "__c10",
    .internalCall "SqrtPriceMath_getAmount1Delta"
      [.var "__c10", .field (.var "_slot0") "sqrtPriceX96", .field (.var "params") "liquidityDelta"]
      "__c11",
    .assign .localVar ⟨"amount1", []⟩ (.var "__c11"),
    .internalCall "LiquidityMath_addDelta"
      [.var "liquidityBefore", .field (.var "params") "liquidityDelta"] "__c12",
    .assign .storage ⟨"liquidity", []⟩ (.var "__c12")]

theorem modifyPositionMiddleOracleArgs_fits (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm : EVM.State) : (modifyPositionMiddleOracleArgs v a evm).Fits := by
  refine ⟨?_, blockTimestampWord_lt _, ?_, poolLiquidityWord_lt _ _, ?_, ?_⟩
  · exact u256LandMaskToNatLtOfToNat (bits := 16) _ _ (by decide)
  · dsimp only [modifyPositionMiddleOracleArgs]
    exact slot0TickValue_bounds evm.accountMap evm.executionEnv
  · exact u256LandMaskToNatLtOfToNat (bits := 16) _ _ (by decide)
  · exact u256LandMaskToNatLtOfToNat (bits := 16) _ _ (by decide)

macro "modify_position_middle_get" : tactic =>
  `(tactic| (simp only [modifyPositionMiddleOracleFrame, modifyPositionMiddleTimeFrame,
    modifyPositionMiddleLiquidityFrame, resumeAfterInternalCall,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; modify_position_updated_get))

theorem modifyPositionMiddleTimeFrame_eq (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm : EVM.State) : modifyPositionMiddleTimeFrame v a evm =
      {contract := contract, locals := (modifyPositionMiddleTimeFrame v a evm).locals,
        immutables := immStore v} := rfl

end Benchmarks.UniswapV3.Pool

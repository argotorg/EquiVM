import Benchmarks.UniswapV3.Pool.UpdatePositionTickModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem evalUpdatePositionTickExprs (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm evm' : EVM.State) (upper : Bool) :
    evalExprs? config (updatePositionTickInputFrame v a evm upper) evm'
      (updatePositionTickExprs upper) = .ok (tickUpdateValues (updatePositionTickArgs v a evm upper)) := by
  let frame := updatePositionTickInputFrame v a evm upper
  have ht : evalExpr? config frame evm' (.var (if upper then "tickUpper" else "tickLower")) =
      .ok (.int (if upper then a.upper else a.lower)) := by
    apply evalExpr_var_get
    cases upper <;> dsimp only [frame] <;> update_position_tick_get
  have hc : evalExpr? config frame evm' (.var "tick") = .ok (.int a.current) := by
    apply evalExpr_var_get
    cases upper <;> dsimp only [frame] <;> update_position_tick_get
  have hd : evalExpr? config frame evm' (.var "liquidityDelta") = .ok (.int a.delta) := by
    apply evalExpr_var_get
    cases upper <;> dsimp only [frame] <;> update_position_tick_get
  have hg0 : evalExpr? config frame evm' (.var "_feeGrowthGlobal0X128") =
      .ok (.int (Int.ofNat (feeGrowthWord false evm.accountMap evm.executionEnv).toNat)) := by
    apply evalExpr_var_get
    cases upper <;> dsimp only [frame] <;> update_position_tick_get
  have hg1 : evalExpr? config frame evm' (.var "_feeGrowthGlobal1X128") =
      .ok (.int (Int.ofNat (feeGrowthWord true evm.accountMap evm.executionEnv).toNat)) := by
    apply evalExpr_var_get
    cases upper <;> dsimp only [frame] <;> update_position_tick_get
  have hs : evalExpr? config frame evm' (.var "secondsPerLiquidityCumulativeX128") =
      .ok (.int (Int.ofNat
        (snapshotCurrent evm.accountMap evm.executionEnv).secondsPerLiquidity.toNat)) := by
    apply evalExpr_var_get
    cases upper <;> dsimp only [frame] <;> update_position_tick_get
  have hcum : evalExpr? config frame evm' (.var "tickCumulative") =
      .ok (.int (snapshotCurrent evm.accountMap evm.executionEnv).tickCumulative) := by
    apply evalExpr_var_get
    cases upper <;> dsimp only [frame] <;> update_position_tick_get
  have htime : evalExpr? config frame evm' (.var "time") =
      .ok (.int (Int.ofNat (blockTimestampWord evm.executionEnv).toNat)) := by
    apply evalExpr_var_get
    cases upper <;> dsimp only [frame] <;> update_position_tick_get
  have hf : frame = {contract := contract, locals := frame.locals, immutables := immStore v} := by
    cases upper <;> rfl
  have hm := evalMaxLiquidityPerTick128 v frame.locals evm'
  rw [← hf] at hm
  change evalExprs? config frame evm' _ = _
  simp only [updatePositionTickExprs, tickUpdateValues, updatePositionTickArgs, evalExprs?,
    ht, hc, hd, hg0, hg1, hs, hcum, htime, hm, evalExpr?, bind, EvalResult.bind, pure]

theorem updatePositionTickCallSource (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) (ha : a.Fits)
    (hv : liquidityDeltaValid
      (tickUpdateGrossBefore (updatePositionTickArgs v a evm upper)
        (updatePositionTickBefore v a evm upper)) a.delta)
    (hm : tickUpdateGrossAfter (updatePositionTickArgs v a evm upper)
      (updatePositionTickBefore v a evm upper) ≤ Int.ofNat (uint128Word v.maxLiquidityPerTick).toNat)
    (hn : safeCast128Valid (tickUpdateNetResult (updatePositionTickArgs v a evm upper)
      (updatePositionTickBefore v a evm upper) upper)) :
    ExecStmt config (updatePositionTickInputFrame v a evm upper)
      (updatePositionTickBefore v a evm upper)
      (.internalCall "Tick_update" (updatePositionTickExprs upper) (if upper then "__c4" else "__c3"))
      (.ok (updatePositionTickCallFrame v a evm upper) (updatePositionTickAfter v a evm upper)) := by
  have hb := tickUpdateReturns (immStore v) (updatePositionTickBefore v a evm upper)
    (updatePositionTickArgs v a evm upper) ha.2.2.1.1 ha.2.2.1.2 hv hm hn
  have he := evalUpdatePositionTickExprs v a evm (updatePositionTickBefore v a evm upper) upper
  have hf : {updatePositionTickInputFrame v a evm upper with
      locals := tickUpdateLocals (updatePositionTickArgs v a evm upper)} =
      tickUpdateFrame (immStore v) (updatePositionTickArgs v a evm upper) := by
    cases upper <;> rfl
  have hc := internalCallFunctionReturn
    (argVals := tickUpdateValues (updatePositionTickArgs v a evm upper))
    (callee := tickUpdateFunction) (locals := tickUpdateLocals (updatePositionTickArgs v a evm upper))
    (calleeSolm := tickUpdateNetReadyFrame (immStore v) (updatePositionTickArgs v a evm upper)
      (updatePositionTickBefore v a evm upper) upper)
    (value := some [.bool (updatePositionFlipped v a evm upper)])
    (retVar := if upper then "__c4" else "__c3") (name := "Tick_update") he
    (by cases upper <;> exact tickUpdateLookup)
    (tickUpdateBind _) (by rw [hf]; exact hb)
  cases upper <;> exact hc

theorem updatePositionTickCallReverts (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool)
    (hb : ExecFuncBody config (tickUpdateFrame (immStore v) (updatePositionTickArgs v a evm upper))
      (updatePositionTickBefore v a evm upper) tickUpdateFunction.body .reverted) :
    ExecStmt config (updatePositionTickInputFrame v a evm upper)
      (updatePositionTickBefore v a evm upper)
      (.internalCall "Tick_update" (updatePositionTickExprs upper) (if upper then "__c4" else "__c3"))
      .reverted := by
  apply internalCallFunctionRevert (callee := tickUpdateFunction)
    (locals := tickUpdateLocals (updatePositionTickArgs v a evm upper))
    (evalUpdatePositionTickExprs v a evm _ upper)
    (by cases upper <;> exact tickUpdateLookup) (tickUpdateBind _)
  cases upper <;> exact hb

theorem updatePositionTickCallStatic (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool)
    (hb : ExecFuncBody config (tickUpdateFrame (immStore v) (updatePositionTickArgs v a evm upper))
      (updatePositionTickBefore v a evm upper) tickUpdateFunction.body .staticViolation) :
    ExecStmt config (updatePositionTickInputFrame v a evm upper)
      (updatePositionTickBefore v a evm upper)
      (.internalCall "Tick_update" (updatePositionTickExprs upper) (if upper then "__c4" else "__c3"))
      .staticViolation := by
  apply ExecStmt.internalCallStatic (callee := tickUpdateFunction.toCallable)
    (locals := tickUpdateLocals (updatePositionTickArgs v a evm upper))
    (evalUpdatePositionTickExprs v a evm _ upper)
    (by cases upper <;> exact tickUpdateLookup) (tickUpdateBind _)
  cases upper <;> exact hb

theorem updatePositionTickAssignSource (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm evm' : EVM.State) (upper : Bool) :
    ExecStmt config (updatePositionTickCallFrame v a evm upper) evm'
      (.assign .localVar ⟨if upper then "flippedUpper" else "flippedLower", []⟩
        (.var (if upper then "__c4" else "__c3")))
      (.ok (updatePositionTickDoneFrame v a evm upper) evm') := by
  cases upper
  all_goals
    exact ExecStmt.assign (evalExpr_var_get (by update_position_tick_get))
      (assignLocalVarBase_frame (old := .bool false) (by update_position_tick_get))

def updatePositionTickBody (upper : Bool) : List Stmt :=
  [.internalCall "Tick_update" (updatePositionTickExprs upper) (if upper then "__c4" else "__c3"),
    .assign .localVar ⟨if upper then "flippedUpper" else "flippedLower", []⟩
      (.var (if upper then "__c4" else "__c3"))]

theorem updatePositionTickSource (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) (ha : a.Fits)
    (hv : liquidityDeltaValid
      (tickUpdateGrossBefore (updatePositionTickArgs v a evm upper)
        (updatePositionTickBefore v a evm upper)) a.delta)
    (hm : tickUpdateGrossAfter (updatePositionTickArgs v a evm upper)
      (updatePositionTickBefore v a evm upper) ≤ Int.ofNat (uint128Word v.maxLiquidityPerTick).toNat)
    (hn : safeCast128Valid (tickUpdateNetResult (updatePositionTickArgs v a evm upper)
      (updatePositionTickBefore v a evm upper) upper)) :
    ExecBlock config (updatePositionTickInputFrame v a evm upper)
      (updatePositionTickBefore v a evm upper) (updatePositionTickBody upper)
      (.ok (updatePositionTickDoneFrame v a evm upper) (updatePositionTickAfter v a evm upper)) :=
  ExecBlock.consNormal (updatePositionTickCallSource v a evm upper ha hv hm hn)
    (ExecBlock.consNormal (updatePositionTickAssignSource v a evm _ upper) ExecBlock.nil)

end Benchmarks.UniswapV3.Pool

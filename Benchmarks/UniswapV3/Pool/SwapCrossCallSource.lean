import Benchmarks.UniswapV3.Pool.SwapCrossFlags
import Benchmarks.UniswapV3.Pool.FeeGrowthStorage
import Benchmarks.UniswapV3.Pool.TickCrossCost
import Benchmarks.UniswapV3.Pool.SourceFrame

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapCrossArgs (zeroForOne : Bool) (c : SwapCacheData) (s : SwapStateData)
    (d : SwapIterationData) (σ : AccountMap) (I : ExecutionEnv) : TickCrossArgs :=
  {tick := d.tickNext
   global0 := if zeroForOne then s.feeGrowth else feeGrowthWord false σ I
   global1 := if zeroForOne then feeGrowthWord true σ I else s.feeGrowth
   secondsPerLiquidity := c.secondsPerLiquidity
   cumulative := c.tickCumulative
   time := c.blockTimestamp}

def swapCrossCallArgs : List Expr :=
  [.field (.var "step") "tickNext",
    .ite (.var "zeroForOne") (.field (.var "state") "feeGrowthGlobalX128")
      (.storage ⟨"feeGrowthGlobal0X128", []⟩),
    .ite (.var "zeroForOne") (.storage ⟨"feeGrowthGlobal1X128", []⟩)
      (.field (.var "state") "feeGrowthGlobalX128"),
    .field (.var "cache") "secondsPerLiquidityCumulativeX128",
    .field (.var "cache") "tickCumulative", .field (.var "cache") "blockTimestamp"]

theorem swapCrossCallStmt : swapInitializedBody[1]! =
    .internalCall "Tick_cross" swapCrossCallArgs "liquidityNet" := rfl

theorem evalSwapCrossCallArgs {frame : Frame} {evm : EVM.State}
    (zeroForOne : Bool) (c : SwapCacheData) (s : SwapStateData) (d : SwapIterationData)
    (hf : frame.contract = contract)
    (hz : frame.locals.get? "zeroForOne" = some (.bool zeroForOne))
    (hc : frame.locals.get? "cache" = some c.value)
    (hs : frame.locals.get? "state" = some s.value)
    (hd : frame.locals.get? "step" = some d.value)
    (hg : ∀ b, frame.locals.get? (feeGrowthName b) = none) :
    evalExprs? config frame evm swapCrossCallArgs =
      .ok (swapCrossArgs zeroForOne c s d evm.accountMap evm.executionEnv).values := by
  have hframe : frame =
      {contract := contract, locals := frame.locals, immutables := frame.immutables} :=
    frame_eq_of_parts hf rfl
  have e0 := evalFeeGrowth frame.locals frame.immutables evm false (hg false)
  have e1 := evalFeeGrowth frame.locals frame.immutables evm true (hg true)
  rw [← hframe] at e0 e1
  have ez := evalExpr_var_get (cfg := config) (evm := evm) hz
  have ec := evalExpr_var_get (cfg := config) (evm := evm) hc
  have et := evalExpr_structField (name := "tickNext")
    (evalExpr_var_get (cfg := config) (evm := evm) hd) rfl
  have ef := evalExpr_structField (name := "feeGrowthGlobalX128")
    (evalExpr_var_get (cfg := config) (evm := evm) hs) rfl
  have esec := evalExpr_structField (name := "secondsPerLiquidityCumulativeX128") ec rfl
  have ecum := evalExpr_structField (name := "tickCumulative") ec rfl
  have etime := evalExpr_structField (name := "blockTimestamp") ec rfl
  have ef0 : evalExpr? config frame evm
      (.ite (.var "zeroForOne") (.field (.var "state") "feeGrowthGlobalX128")
        (.storage ⟨"feeGrowthGlobal0X128", []⟩)) =
      .ok (.int (Int.ofNat
        (if zeroForOne then s.feeGrowth else feeGrowthWord false evm.accountMap
          evm.executionEnv).toNat)) := by
    cases zeroForOne
    · simpa only [evalExpr?, ez, bind, EvalResult.bind] using e0
    · simpa only [evalExpr?, ez, bind, EvalResult.bind] using ef
  have ef1 : evalExpr? config frame evm
      (.ite (.var "zeroForOne") (.storage ⟨"feeGrowthGlobal1X128", []⟩)
        (.field (.var "state") "feeGrowthGlobalX128")) =
      .ok (.int (Int.ofNat
        (if zeroForOne then feeGrowthWord true evm.accountMap evm.executionEnv
          else s.feeGrowth).toNat)) := by
    cases zeroForOne
    · simpa only [evalExpr?, ez, bind, EvalResult.bind] using ef
    · simpa only [evalExpr?, ez, bind, EvalResult.bind] using e1
  simp only [swapCrossCallArgs, evalExprs?, et, ef0, ef1, esec, ecum, etime,
    bind, EvalResult.bind, pure]
  rfl

end Benchmarks.UniswapV3.Pool

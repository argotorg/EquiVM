import Benchmarks.UniswapV3.Pool.TickUpdateCheckedSource
import Benchmarks.UniswapV3.Pool.TickHistoryStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def tickUpdateOutsideState (a : TickUpdateArgs) (evm : EVM.State) : EVM.State :=
  let e0 := tickFeeOutsideState evm a.tick false a.global0
  let e1 := tickFeeOutsideState e0 a.tick true a.global1
  let e2 := tickHistoryState e1 a.tick .secondsPerLiquidity a.secondsPerLiquidity
  let e3 := tickHistoryState e2 a.tick .cumulative (EVM.wordOfInt a.cumulative)
  tickHistoryState e3 a.tick .seconds a.time

def tickUpdateInitializedState (a : TickUpdateArgs) (evm : EVM.State) : EVM.State :=
  if tickUpdateGrossBefore a evm = 0 then
    tickHistoryState (if a.tick ≤ a.current then tickUpdateOutsideState a evm else evm)
      a.tick .initialized ⟨1⟩
  else evm

def tickUpdateGrossState (a : TickUpdateArgs) (evm : EVM.State) : EVM.State :=
  tickLiquidityState (tickUpdateInitializedState a evm) a.tick false
    (EVM.wordOfInt (tickUpdateGrossAfter a evm))

theorem tickUpdateOutsideState_executionEnv (a : TickUpdateArgs) (evm : EVM.State) :
    (tickUpdateOutsideState a evm).executionEnv = evm.executionEnv := by
  simp only [tickUpdateOutsideState, tickFeeOutsideState_executionEnv, tickHistoryState_executionEnv]

theorem tickUpdateInitializedState_executionEnv (a : TickUpdateArgs) (evm : EVM.State) :
    (tickUpdateInitializedState a evm).executionEnv = evm.executionEnv := by
  unfold tickUpdateInitializedState
  split
  · rw [tickHistoryState_executionEnv]
    split
    · exact tickUpdateOutsideState_executionEnv a evm
    · rfl
  · rfl

def tickUpdateOutsideBody : List Stmt :=
  [.assign .storage ⟨"info", [.field "feeGrowthOutside0X128"]⟩ (.var "feeGrowthGlobal0X128"),
   .assign .storage ⟨"info", [.field "feeGrowthOutside1X128"]⟩ (.var "feeGrowthGlobal1X128"),
   .assign .storage ⟨"info", [.field "secondsPerLiquidityOutsideX128"]⟩
     (.var "secondsPerLiquidityCumulativeX128"),
   .assign .storage ⟨"info", [.field "tickCumulativeOutside"]⟩ (.var "tickCumulative"),
   .assign .storage ⟨"info", [.field "secondsOutside"]⟩ (.var "time")]

theorem tickUpdateOutsideSource (imms : Store) (evm : EVM.State) (a : TickUpdateArgs) :
    ExecBlock config (tickUpdateFlippedFrame imms a evm) evm tickUpdateOutsideBody
      (.ok (tickUpdateFlippedFrame imms a evm) (tickUpdateOutsideState a evm)) := by
  let frame := tickUpdateFlippedFrame imms a evm
  have hg : frame.locals.get? "info" = some (tickAlias a.tick) := by dsimp only [frame]; tick_update_get
  let e0 := tickFeeOutsideState evm a.tick false a.global0
  let e1 := tickFeeOutsideState e0 a.tick true a.global1
  let e2 := tickHistoryState e1 a.tick .secondsPerLiquidity a.secondsPerLiquidity
  let e3 := tickHistoryState e2 a.tick .cumulative (EVM.wordOfInt a.cumulative)
  have h0 : ExecStmt config frame evm
      (.assign .storage ⟨"info", [.field "feeGrowthOutside0X128"]⟩ (.var "feeGrowthGlobal0X128"))
      (.ok frame e0) :=
    ExecStmt.assign (evalExpr_var_get (by dsimp only [frame]; tick_update_get))
      (assignTickFeeOutside frame.locals imms evm "info" a.tick false a.global0 hg)
  have h1 : ExecStmt config frame e0
      (.assign .storage ⟨"info", [.field "feeGrowthOutside1X128"]⟩ (.var "feeGrowthGlobal1X128"))
      (.ok frame e1) :=
    ExecStmt.assign (evalExpr_var_get (by dsimp only [frame]; tick_update_get))
      (assignTickFeeOutside frame.locals imms e0 "info" a.tick true a.global1 hg)
  have h2 : ExecStmt config frame e1
      (.assign .storage ⟨"info", [.field "secondsPerLiquidityOutsideX128"]⟩
        (.var "secondsPerLiquidityCumulativeX128")) (.ok frame e2) :=
    ExecStmt.assign (evalExpr_var_get (by dsimp only [frame]; tick_update_get))
      (assignTickHistory frame.locals imms e1 "info" a.tick .secondsPerLiquidity
        (.int (Int.ofNat a.secondsPerLiquidity.toNat)) a.secondsPerLiquidity hg
        (by simp only [valueToWord, wordOfInt_ofNat_toNat, pure]))
  have h3 : ExecStmt config frame e2
      (.assign .storage ⟨"info", [.field "tickCumulativeOutside"]⟩ (.var "tickCumulative"))
      (.ok frame e3) :=
    ExecStmt.assign (evalExpr_var_get (by dsimp only [frame]; tick_update_get))
      (assignTickHistory frame.locals imms e2 "info" a.tick .cumulative (.int a.cumulative)
        (EVM.wordOfInt a.cumulative) hg rfl)
  have h4 : ExecStmt config frame e3
      (.assign .storage ⟨"info", [.field "secondsOutside"]⟩ (.var "time"))
      (.ok frame (tickUpdateOutsideState a evm)) :=
    ExecStmt.assign (evalExpr_var_get (by dsimp only [frame]; tick_update_get))
      (assignTickHistory frame.locals imms e3 "info" a.tick .seconds
        (.int (Int.ofNat a.time.toNat)) a.time hg
        (by simp only [valueToWord, wordOfInt_ofNat_toNat, pure]))
  exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consNormal h2
    (ExecBlock.consNormal h3 (ExecBlock.consNormal h4 ExecBlock.nil))))

theorem evalTickUpdateInitConditions (imms : Store) (evm : EVM.State) (a : TickUpdateArgs) :
    evalExpr? config (tickUpdateFlippedFrame imms a evm) evm
      (.binary .eq (.var "liquidityGrossBefore") (.intLit 0)) =
      .ok (.bool (decide (tickUpdateGrossBefore a evm = 0))) ∧
    evalExpr? config (tickUpdateFlippedFrame imms a evm) evm
      (.binary .le (.var "tick") (.var "tickCurrent")) =
      .ok (.bool (decide (a.tick ≤ a.current))) := by
  have hg := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := tickUpdateFlippedFrame imms a evm) (name := "liquidityGrossBefore")
    (value := .int (tickUpdateGrossBefore a evm)) (by tick_update_get)
  have ht := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := tickUpdateFlippedFrame imms a evm) (name := "tick")
    (value := .int a.tick) (by tick_update_get)
  have hc := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := tickUpdateFlippedFrame imms a evm) (name := "tickCurrent")
    (value := .int a.current) (by tick_update_get)
  constructor
  · by_cases hz : tickUpdateGrossBefore a evm = 0 <;>
      simp [evalExpr?, hg, evalBinaryOp?, bind, EvalResult.bind, pure, hz]
  · simp only [evalExpr?, ht, hc, evalBinaryOp?, bind, EvalResult.bind]

theorem tickUpdateInitializedSource (imms : Store) (evm : EVM.State) (a : TickUpdateArgs) :
    ExecStmt config (tickUpdateFlippedFrame imms a evm) evm (tickUpdateFunction.body[6]!)
      (.ok (tickUpdateFlippedFrame imms a evm) (tickUpdateInitializedState a evm)) := by
  have hc := evalTickUpdateInitConditions imms evm a
  by_cases hz : tickUpdateGrossBefore a evm = 0
  · simp only [tickUpdateInitializedState, if_pos hz]
    apply ExecStmt.iteTrue (by simpa only [hz, decide_true] using hc.1)
    have hout : ExecStmt config (tickUpdateFlippedFrame imms a evm) evm
        (.ite (.binary .le (.var "tick") (.var "tickCurrent")) tickUpdateOutsideBody [])
        (.ok (tickUpdateFlippedFrame imms a evm)
          (if a.tick ≤ a.current then tickUpdateOutsideState a evm else evm)) := by
      by_cases ht : a.tick ≤ a.current
      · rw [if_pos ht]
        exact ExecStmt.iteTrue (by simpa only [ht, decide_true] using hc.2)
          (tickUpdateOutsideSource imms evm a)
      · rw [if_neg ht]
        exact ExecStmt.iteFalse (by simpa only [ht, decide_false] using hc.2) ExecBlock.nil
    refine ExecBlock.consNormal hout ?_
    exact ExecBlock.consNormal (ExecStmt.assign (by simp only [evalExpr?, pure])
      (assignTickHistory (tickUpdateFlippedFrame imms a evm).locals imms _ "info" a.tick
        .initialized (.bool true) ⟨1⟩ (by tick_update_get) rfl)) ExecBlock.nil
  · simp only [tickUpdateInitializedState, if_neg hz]
    exact ExecStmt.iteFalse (by simpa only [hz, decide_false] using hc.1) ExecBlock.nil

theorem tickUpdateGrossSource (imms : Store) (evm : EVM.State) (a : TickUpdateArgs) :
    ExecStmt config (tickUpdateFlippedFrame imms a evm) (tickUpdateInitializedState a evm)
      (tickUpdateFunction.body[7]!)
      (.ok (tickUpdateFlippedFrame imms a evm) (tickUpdateGrossState a evm)) := by
  exact ExecStmt.assign (evalExpr_var_get (by tick_update_get))
    (assignTickLiquidity (tickUpdateFlippedFrame imms a evm).locals imms _ "info" a.tick false
      (.int (tickUpdateGrossAfter a evm)) (EVM.wordOfInt (tickUpdateGrossAfter a evm))
      (by tick_update_get) rfl)

theorem tickUpdateStoresSource (imms : Store) (evm : EVM.State) (a : TickUpdateArgs)
    (hv : liquidityDeltaValid (tickUpdateGrossBefore a evm) a.delta)
    (hm : tickUpdateGrossAfter a evm ≤ Int.ofNat a.maxLiquidity.toNat) :
    ExecBlock config (tickUpdateFrame imms a) evm (tickUpdateFunction.body.take 8)
      (.ok (tickUpdateFlippedFrame imms a evm) (tickUpdateGrossState a evm)) := by
  change ExecBlock config (tickUpdateFrame imms a) evm
    (tickUpdateFunction.body.take 6 ++ [tickUpdateFunction.body[6]!, tickUpdateFunction.body[7]!]) _
  exact execBlock_append_ok (tickUpdateCheckedSource imms evm a hv hm)
    (ExecBlock.consNormal (tickUpdateInitializedSource imms evm a)
      (ExecBlock.consNormal (tickUpdateGrossSource imms evm a) ExecBlock.nil))

end Benchmarks.UniswapV3.Pool

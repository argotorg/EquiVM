import Benchmarks.UniswapV3.Pool.PositionUpdateFeesSource
import Benchmarks.UniswapV3.Pool.PositionUpdateStoreModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem evalPositionUpdateNonzero (imms : Store) (original current : EVM.State)
    (a : PositionUpdateArgs) :
    evalExpr? config (positionUpdateReadyFrame imms a original) current
      (.binary .ne (.var "liquidityDelta") (.intLit 0)) = .ok (.bool (decide (a.delta ≠ 0))) := by
  have he := evalExpr_var_get (cfg := config) (evm := current)
    (frame := positionUpdateReadyFrame imms a original) (name := "liquidityDelta")
    (value := .int a.delta) (by position_update_ready_get)
  simp [evalExpr?, he, evalBinaryOp?, bind, EvalResult.bind, pure]
  apply Bool.eq_iff_iff.mpr
  simp

theorem positionUpdateLiquidityStore (imms : Store) (evm : EVM.State) (a : PositionUpdateArgs) :
    ExecStmt config (positionUpdateReadyFrame imms a evm) evm
      (.assign .storage ⟨"self", [.field "liquidity"]⟩ (.var "liquidityNext"))
      (.ok (positionUpdateReadyFrame imms a evm)
        (positionLiquidityState evm a.key (EVM.wordOfInt (positionUpdateLiquidityNext a evm)))) := by
  rw [positionUpdateReadyFrame_eq imms a evm]
  exact ExecStmt.assign (evalExpr_var_get (by position_update_ready_get))
    (assignPositionLiquidity _ imms evm "self" a.key (positionUpdateLiquidityNext a evm)
      (by position_update_ready_get))

theorem positionUpdateLiquidityStoreChoice (imms : Store) (evm : EVM.State)
    (a : PositionUpdateArgs) :
    ExecStmt config (positionUpdateReadyFrame imms a evm) evm (positionUpdateFunction.body[8]!)
      (.ok (positionUpdateReadyFrame imms a evm) (positionUpdateLiquidityState a evm)) := by
  have hc := evalPositionUpdateNonzero imms evm evm a
  by_cases hz : a.delta = 0
  · simp only [positionUpdateLiquidityState, if_pos hz]
    exact ExecStmt.iteFalse (by simpa only [hz, ne_eq, not_true_eq_false, decide_false] using hc)
      ExecBlock.nil
  · simp only [positionUpdateLiquidityState, if_neg hz]
    exact ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using hc)
      (ExecBlock.consNormal (positionUpdateLiquidityStore imms evm a) ExecBlock.nil)

theorem positionUpdateGrowthStore (imms : Store) (original current : EVM.State)
    (a : PositionUpdateArgs) (second : Bool) :
    ExecStmt config (positionUpdateReadyFrame imms a original) current
      (.assign .storage ⟨"self", [.field (positionLastField second)]⟩
        (.var (positionUpdateGrowthName second)))
      (.ok (positionUpdateReadyFrame imms a original)
        (positionLastState current a.key second (a.growth second))) := by
  rw [positionUpdateReadyFrame_eq imms a original]
  exact ExecStmt.assign (evalExpr_var_get (by cases second <;> position_update_ready_get))
    (assignPositionLast _ imms current "self" a.key second (a.growth second)
      (by position_update_ready_get))

theorem positionUpdateStoresSource (imms : Store) (evm : EVM.State)
    (a : PositionUpdateArgs) (hv : positionUpdateLiquidityValid a evm) :
    ExecBlock config (positionUpdateFrame imms a) evm (positionUpdateFunction.body.take 11)
      (.ok (positionUpdateReadyFrame imms a evm) (positionUpdateGrowthState a evm)) := by
  change ExecBlock config (positionUpdateFrame imms a) evm
    (positionUpdateFunction.body.take 8 ++ (positionUpdateFunction.body.drop 8).take 3) _
  exact execBlock_append_ok (positionUpdateFeesSource imms evm a hv)
    (ExecBlock.consNormal (positionUpdateLiquidityStoreChoice imms evm a)
      (ExecBlock.consNormal (positionUpdateGrowthStore imms evm _ a false)
        (ExecBlock.consNormal (positionUpdateGrowthStore imms evm _ a true) ExecBlock.nil)))

theorem evalPositionUpdateFeesGuard (imms : Store) (original current : EVM.State)
    (a : PositionUpdateArgs) :
    evalExpr? config (positionUpdateReadyFrame imms a original) current
      (.binary .or (.binary .gt (.var "tokensOwed0") (.intLit 0))
        (.binary .gt (.var "tokensOwed1") (.intLit 0))) =
      .ok (.bool (positionUpdateHasFees a original)) := by
  apply evalExpr_bool_or
  · exact evalExpr_word_gt (a := positionUpdateOwed a original false) (b := ⟨0⟩)
      (evalExpr_var_get (by position_update_ready_get)) (by simp only [evalExpr?, pure]; rfl)
  · exact evalExpr_word_gt (a := positionUpdateOwed a original true) (b := ⟨0⟩)
      (evalExpr_var_get (by position_update_ready_get)) (by simp only [evalExpr?, pure]; rfl)

theorem positionUpdateOwedStore (imms : Store) (original current : EVM.State)
    (a : PositionUpdateArgs) (second : Bool) :
    ExecStmt config (positionUpdateReadyFrame imms a original) current (positionUpdateOwedStmt second)
      (.ok (positionUpdateReadyFrame imms a original)
        (positionUpdateOwedState a original current second)) := by
  rw [positionUpdateReadyFrame_eq imms a original]
  exact positionUpdateOwedSource _ imms original current a second
    (by position_update_ready_get) (by cases second <;> position_update_ready_get)

theorem positionUpdateOwedChoice (imms : Store) (evm : EVM.State) (a : PositionUpdateArgs) :
    ExecStmt config (positionUpdateReadyFrame imms a evm) (positionUpdateGrowthState a evm)
      (positionUpdateFunction.body[11]!)
      (.ok (positionUpdateReadyFrame imms a evm) (positionUpdateFinalState a evm)) := by
  have hc := evalPositionUpdateFeesGuard imms evm (positionUpdateGrowthState a evm) a
  cases hf : positionUpdateHasFees a evm
  · simp only [positionUpdateFinalState, hf, Bool.false_eq_true, if_false]
    exact ExecStmt.iteFalse (by simpa only [hf] using hc) ExecBlock.nil
  · simp only [positionUpdateFinalState, hf, if_true]
    exact ExecStmt.iteTrue (by simpa only [hf] using hc)
      (ExecBlock.consNormal (positionUpdateOwedStore imms evm _ a false)
        (ExecBlock.consNormal (positionUpdateOwedStore imms evm _ a true) ExecBlock.nil))

end Benchmarks.UniswapV3.Pool

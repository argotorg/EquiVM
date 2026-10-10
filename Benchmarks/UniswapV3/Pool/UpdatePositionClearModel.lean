import Benchmarks.UniswapV3.Pool.UpdatePositionPositionSource
import Benchmarks.UniswapV3.Pool.TickClearInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def updatePositionClearLowerFrame (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : Frame :=
  if updatePositionFlag v a evm false then
    resumeAfterInternalCall (updatePositionPositionFrame v a evm) "__c9" none
  else updatePositionPositionFrame v a evm

def updatePositionClearInputFrame (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : Frame :=
  if upper then updatePositionClearLowerFrame v a evm else updatePositionPositionFrame v a evm

def updatePositionClearDoneFrame (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : Frame :=
  if updatePositionFlag v a evm upper then
    resumeAfterInternalCall (updatePositionClearInputFrame v a evm upper)
      (if upper then "__c10" else "__c9") none
  else updatePositionClearInputFrame v a evm upper

def updatePositionClearLowerState (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : EVM.State :=
  if updatePositionFlag v a evm false then
    tickClearState (updatePositionPositionState v a evm) a.lower
  else updatePositionPositionState v a evm

def updatePositionClearBefore (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : EVM.State :=
  if upper then updatePositionClearLowerState v a evm else updatePositionPositionState v a evm

def updatePositionClearAfter (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : EVM.State :=
  if updatePositionFlag v a evm upper then
    tickClearState (updatePositionClearBefore v a evm upper) (if upper then a.upper else a.lower)
  else updatePositionClearBefore v a evm upper

def updatePositionClearExprs (upper : Bool) : List Expr :=
  [.var (if upper then "tickUpper" else "tickLower")]

def updatePositionClearStmt (upper : Bool) : Stmt :=
  .ite (.var (if upper then "flippedUpper" else "flippedLower"))
    [.internalCall "Tick_clear" (updatePositionClearExprs upper) (if upper then "__c10" else "__c9")]
    []

theorem updatePositionClearInputFrame_eq (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) :
    updatePositionClearInputFrame v a evm upper =
      {contract := contract, locals := (updatePositionClearInputFrame v a evm upper).locals,
        immutables := immStore v} := by
  unfold updatePositionClearInputFrame updatePositionClearLowerFrame updatePositionPositionFrame
  rw [updatePositionFee1Frame_eq]
  split_ifs <;> rfl

macro "update_position_clear_get" : tactic =>
  `(tactic| (simp only [updatePositionClearDoneFrame, updatePositionClearInputFrame,
    updatePositionClearLowerFrame, updatePositionPositionFrame, resumeAfterInternalCall,
    updatePositionFee1Frame, updatePositionFee0Frame, updatePositionFeeFrame,
    updatePositionChangedFrame, updatePositionBitmapDoneFrame, updatePositionBitmapCallFrame,
    updatePositionBitmapInputFrame, updatePositionBitmapLowerFrame,
    Bool.false_eq_true, if_false, if_true]; (try split_ifs) <;>
    ((try simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]);
      (first | update_position_tick_get | update_position_prefix_get | rfl))))

theorem evalUpdatePositionClearExprs (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm evm' : EVM.State) (upper : Bool) :
    evalExprs? config (updatePositionClearInputFrame v a evm upper) evm'
      (updatePositionClearExprs upper) = .ok [.int (if upper then a.upper else a.lower)] := by
  have ht : evalExpr? config (updatePositionClearInputFrame v a evm upper) evm'
      (.var (if upper then "tickUpper" else "tickLower")) =
      .ok (.int (if upper then a.upper else a.lower)) := by
    apply evalExpr_var_get
    cases upper <;> update_position_clear_get
  simp only [updatePositionClearExprs, evalExprs?, ht, bind, EvalResult.bind, pure]

theorem evalUpdatePositionClearGuard (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm evm' : EVM.State) (upper : Bool) :
    evalExpr? config (updatePositionClearInputFrame v a evm upper) evm'
      (.var (if upper then "flippedUpper" else "flippedLower")) =
      .ok (.bool (updatePositionFlag v a evm upper)) := by
  apply evalExpr_var_get
  cases upper <;> by_cases hz : a.delta = 0
  all_goals
    simp only [updatePositionFlag, hz, if_true, if_false]
    simp only [updatePositionClearInputFrame, updatePositionClearLowerFrame,
      updatePositionPositionFrame, resumeAfterInternalCall, updatePositionFee1Frame,
      updatePositionFee0Frame, updatePositionFeeFrame, updatePositionChangedFrame, hz,
      updatePositionBitmapDoneFrame, updatePositionBitmapCallFrame,
      updatePositionBitmapInputFrame, updatePositionBitmapLowerFrame,
      if_true, Bool.false_eq_true, if_false]
    (try split_ifs) <;>
      (try simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]) <;>
      first | update_position_tick_get | update_position_prefix_get | rfl

theorem evalUpdatePositionNegative (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm evm' : EVM.State) :
    evalExpr? config (updatePositionPositionFrame v a evm) evm'
      (.binary .lt (.var "liquidityDelta") (.intLit 0)) = .ok (.bool (decide (a.delta < 0))) := by
  have hd : evalExpr? config (updatePositionPositionFrame v a evm) evm' (.var "liquidityDelta") =
      .ok (.int a.delta) := evalExpr_var_get (by update_position_clear_get)
  simp only [evalExpr?, hd, bind, EvalResult.bind, evalBinaryOp?, pure]

end Benchmarks.UniswapV3.Pool

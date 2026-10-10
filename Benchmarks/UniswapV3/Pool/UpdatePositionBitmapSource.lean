import Benchmarks.UniswapV3.Pool.UpdatePositionBitmapModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem evalUpdatePositionBitmapExprs (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm evm' : EVM.State) (upper : Bool) :
    evalExprs? config (updatePositionBitmapInputFrame v a evm upper) evm'
      (updatePositionBitmapExprs upper) =
      .ok [.int (if upper then a.upper else a.lower), .int (positionTick v.tickSpacing)] := by
  have ht : evalExpr? config (updatePositionBitmapInputFrame v a evm upper) evm'
      (.var (if upper then "tickUpper" else "tickLower")) =
      .ok (.int (if upper then a.upper else a.lower)) := by
    apply evalExpr_var_get
    cases upper <;> update_position_bitmap_get
  have hs := evalPoolTickSpacing24 v (updatePositionBitmapInputFrame v a evm upper).locals evm'
  rw [← updatePositionBitmapInputFrame_eq v a evm upper] at hs
  simp only [updatePositionBitmapExprs, evalExprs?, ht, hs, bind, EvalResult.bind, pure]

theorem evalUpdatePositionBitmapGuard (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm evm' : EVM.State) (upper : Bool) :
    evalExpr? config (updatePositionBitmapInputFrame v a evm upper) evm'
      (.var (if upper then "flippedUpper" else "flippedLower")) =
      .ok (.bool (updatePositionFlipped v a evm upper)) := by
  apply evalExpr_var_get
  cases upper <;> update_position_bitmap_get

theorem updatePositionBitmapSkip (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) (hf : updatePositionFlipped v a evm upper = false) :
    ExecStmt config (updatePositionBitmapInputFrame v a evm upper)
      (updatePositionBitmapBefore v a evm upper) (updatePositionBitmapStmt upper)
      (.ok (updatePositionBitmapDoneFrame v a evm upper) (updatePositionBitmapAfter v a evm upper)) := by
  simp only [updatePositionBitmapDoneFrame, updatePositionBitmapAfter, hf,
    Bool.false_eq_true, if_false]
  exact ExecStmt.iteFalse (by rw [evalUpdatePositionBitmapGuard, hf]) ExecBlock.nil

theorem updatePositionBitmapSuccess (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) (hf : updatePositionFlipped v a evm upper = true)
    (hb : ExecStmt config (updatePositionBitmapInputFrame v a evm upper)
      (updatePositionBitmapBefore v a evm upper)
      (.internalCall "TickBitmap_flipTick" (updatePositionBitmapExprs upper)
        (if upper then "__c6" else "__c5"))
      (.ok (updatePositionBitmapCallFrame v a evm upper)
        (updatePositionBitmapApply v a (updatePositionBitmapBefore v a evm upper) upper))) :
    ExecStmt config (updatePositionBitmapInputFrame v a evm upper)
      (updatePositionBitmapBefore v a evm upper) (updatePositionBitmapStmt upper)
      (.ok (updatePositionBitmapDoneFrame v a evm upper) (updatePositionBitmapAfter v a evm upper)) := by
  simp only [updatePositionBitmapDoneFrame, updatePositionBitmapAfter, hf, if_true]
  exact ExecStmt.iteTrue (by rw [evalUpdatePositionBitmapGuard, hf])
    (ExecBlock.consNormal hb ExecBlock.nil)

theorem updatePositionBitmapReverts (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) (hf : updatePositionFlipped v a evm upper = true)
    (hb : ExecStmt config (updatePositionBitmapInputFrame v a evm upper)
      (updatePositionBitmapBefore v a evm upper)
      (.internalCall "TickBitmap_flipTick" (updatePositionBitmapExprs upper)
        (if upper then "__c6" else "__c5")) .reverted) :
    ExecStmt config (updatePositionBitmapInputFrame v a evm upper)
      (updatePositionBitmapBefore v a evm upper) (updatePositionBitmapStmt upper) .reverted :=
  ExecStmt.iteTrue (by rw [evalUpdatePositionBitmapGuard, hf]) (ExecBlock.consRevert hb)

theorem updatePositionBitmapStatic (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) (hf : updatePositionFlipped v a evm upper = true)
    (hb : ExecStmt config (updatePositionBitmapInputFrame v a evm upper)
      (updatePositionBitmapBefore v a evm upper)
      (.internalCall "TickBitmap_flipTick" (updatePositionBitmapExprs upper)
        (if upper then "__c6" else "__c5")) .staticViolation) :
    ExecStmt config (updatePositionBitmapInputFrame v a evm upper)
      (updatePositionBitmapBefore v a evm upper) (updatePositionBitmapStmt upper) .staticViolation :=
  ExecStmt.iteTrue (by rw [evalUpdatePositionBitmapGuard, hf]) (ExecBlock.consStatic hb)

end Benchmarks.UniswapV3.Pool

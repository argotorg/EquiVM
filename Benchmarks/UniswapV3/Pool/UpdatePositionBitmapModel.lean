import Benchmarks.UniswapV3.Pool.UpdatePositionTickSource
import Benchmarks.UniswapV3.Pool.BitmapFlipSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def updatePositionBitmapLowerFrame (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : Frame :=
  let frame := updatePositionUpperFrame v a evm
  if updatePositionFlipped v a evm false then
    {frame with locals := frame.locals.insert "__c5" .unit} else frame

def updatePositionBitmapInputFrame (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : Frame :=
  if upper then updatePositionBitmapLowerFrame v a evm else updatePositionUpperFrame v a evm

def updatePositionBitmapCallFrame (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : Frame :=
  let frame := updatePositionBitmapInputFrame v a evm upper
  {frame with locals := frame.locals.insert (if upper then "__c6" else "__c5") .unit}

def updatePositionBitmapDoneFrame (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : Frame :=
  if updatePositionFlipped v a evm upper then updatePositionBitmapCallFrame v a evm upper
  else updatePositionBitmapInputFrame v a evm upper

def updatePositionBitmapApply (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : EVM.State :=
  let tick := if upper then a.upper else a.lower
  flipBitmap evm (bitmapWordPos (tick.tdiv (positionTick v.tickSpacing)))
    (bitmapFlipMask tick (positionTick v.tickSpacing))

def updatePositionBitmapLowerState (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : EVM.State :=
  if updatePositionFlipped v a evm false then
    updatePositionBitmapApply v a (updatePositionTickAfter v a evm true) false
  else updatePositionTickAfter v a evm true

def updatePositionBitmapBefore (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : EVM.State :=
  if upper then updatePositionBitmapLowerState v a evm else updatePositionTickAfter v a evm true

def updatePositionBitmapAfter (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : EVM.State :=
  if updatePositionFlipped v a evm upper then
    updatePositionBitmapApply v a (updatePositionBitmapBefore v a evm upper) upper
  else updatePositionBitmapBefore v a evm upper

def updatePositionBitmapExprs (upper : Bool) : List Expr :=
  [.var (if upper then "tickUpper" else "tickLower"),
    .cast (.immutable "tickSpacing") (.elem (.int (.sint ⟨24, by decide⟩)))]

def updatePositionBitmapStmt (upper : Bool) : Stmt :=
  .ite (.var (if upper then "flippedUpper" else "flippedLower"))
    [.internalCall "TickBitmap_flipTick" (updatePositionBitmapExprs upper)
      (if upper then "__c6" else "__c5")] []

theorem updatePositionBitmapInputFrame_eq (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) :
    updatePositionBitmapInputFrame v a evm upper =
      {contract := contract, locals := (updatePositionBitmapInputFrame v a evm upper).locals,
        immutables := immStore v} := by
  cases upper
  · rfl
  · unfold updatePositionBitmapInputFrame updatePositionBitmapLowerFrame
    split_ifs <;> rfl

macro "update_position_bitmap_get" : tactic =>
  `(tactic| (simp only [updatePositionBitmapCallFrame, updatePositionBitmapInputFrame,
    updatePositionBitmapLowerFrame, Bool.false_eq_true, if_false, if_true]; (try split_ifs) <;>
    (simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; update_position_tick_get)))

theorem evalPoolTickSpacing24 (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State) :
    evalExpr? config {contract := contract, locals := locals, immutables := immStore v} evm
      (.cast (.immutable "tickSpacing") (.elem (.int (.sint ⟨24, by decide⟩)))) =
      .ok (.int (positionTick v.tickSpacing)) :=
  evalExpr_intCast (.sint ⟨24, by decide⟩) (evalImmutable_tickSpacing config contract locals evm v)

end Benchmarks.UniswapV3.Pool

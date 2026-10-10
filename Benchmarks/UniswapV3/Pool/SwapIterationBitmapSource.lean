import Benchmarks.UniswapV3.Pool.SwapIterationSource
import Benchmarks.UniswapV3.Pool.BitmapNextCostInternal
import Benchmarks.UniswapV3.Pool.PositionGetSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapIterationBitmapArgs : List Expr :=
  [.field (.var "state") "tick",
    .cast (.immutable "tickSpacing") (.elem (.int (.sint ⟨24, by decide⟩))), .var "zeroForOne"]

def swapIterationInputFrame (frame : Frame) (s : SwapStateData) : Frame :=
  swapIterationFrame (swapIterationFrame frame (swapIterationInitial ⟨0⟩))
    (swapIterationInitial s.price)

def swapIterationCompressed (v : UniswapV3PoolImmutables) (s : SwapStateData) : Int :=
  bitmapNextCompressed s.tick (positionTick v.tickSpacing)

def swapIterationMask (v : UniswapV3PoolImmutables) (a : SwapArgs) (s : SwapStateData)
    (evm : EVM.State) : UInt256 :=
  bitmapNextMasked evm (swapIterationCompressed v s) a.zeroForOne

def swapIterationNextTick (v : UniswapV3PoolImmutables) (a : SwapArgs) (s : SwapStateData)
    (evm : EVM.State) : Int :=
  bitmapNextResult (swapIterationCompressed v s) (positionTick v.tickSpacing) a.zeroForOne
    (swapIterationMask v a s evm)

def swapIterationInitialized (v : UniswapV3PoolImmutables) (a : SwapArgs) (s : SwapStateData)
    (evm : EVM.State) : Bool := decide (swapIterationMask v a s evm ≠ ⟨0⟩)

def swapIterationRawNext (v : UniswapV3PoolImmutables) (a : SwapArgs) (s : SwapStateData)
    (evm : EVM.State) : UInt256 :=
  bitmapNextResultRaw (swapIterationCompressed v s) (wordsOf (immStore v) "tickSpacing")
    a.zeroForOne (swapIterationMask v a s evm)

def swapIterationBitmapFrame (frame : Frame) (v : UniswapV3PoolImmutables) (a : SwapArgs)
    (s : SwapStateData) (evm : EVM.State) : Frame :=
  resumeAfterInternalCall (swapIterationInputFrame frame s) "__c2"
    (some [.int (swapIterationNextTick v a s evm), .bool (swapIterationInitialized v a s evm)])

theorem swapIterationInitSource {frame : Frame} {evm : EVM.State} (s : SwapStateData)
    (hs : frame.locals.get? "state" = some s.value) :
    ExecBlock config frame evm (swapLoopBody.take 2)
      (.ok (swapIterationInputFrame frame s) evm) := by
  exact ExecBlock.consNormal (swapIterationZeroSource frame evm)
    (ExecBlock.consNormal (swapIterationStartSource s (swapIterationInitial ⟨0⟩)
      (by simpa only [swapIterationFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, show ("step" == "state") = false from rfl] using hs)
      Std.HashMap.getElem?_insert_self) ExecBlock.nil)

theorem evalSwapIterationBitmapArgs {frame : Frame} {evm : EVM.State}
    (v : UniswapV3PoolImmutables) (a : SwapArgs) (s : SwapStateData)
    (hs : frame.locals.get? "state" = some s.value)
    (hz : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (hi : frame.immutables = immStore v) :
    evalExprs? config frame evm swapIterationBitmapArgs =
      .ok [.int s.tick, .int (positionTick v.tickSpacing), .bool a.zeroForOne] := by
  have ht := evalExpr_structField (name := "tick")
    (evalExpr_var_get (cfg := config) (evm := evm) hs) rfl
  have hzero := evalExpr_var_get (cfg := config) (evm := evm) hz
  have hspacing : evalExpr? config frame evm
      (.cast (.immutable "tickSpacing") (.elem (.int (.sint ⟨24, by decide⟩)))) =
      .ok (.int (positionTick v.tickSpacing)) := by
    apply evalExpr_intCast
    simp only [evalExpr?, hi, immStore_get_tickSpacing, EvalResult.ofOption]
  simp only [swapIterationBitmapArgs, evalExprs?, ht, hspacing, hzero,
    bind, EvalResult.bind, pure]

theorem swapIterationBitmapStmt :
    swapLoopBody[2]! =
      .internalCall "TickBitmap_nextInitializedTickWithinOneWord" swapIterationBitmapArgs "__c2" :=
  rfl

end Benchmarks.UniswapV3.Pool

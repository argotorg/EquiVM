import Benchmarks.UniswapV3.Pool.SwapIterationBitmapSource
import Benchmarks.UniswapV3.Pool.SwapIterationTickSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapIterationNextTick_fits (v : UniswapV3PoolImmutables) (a : SwapArgs)
    (s : SwapStateData) (evm : EVM.State) :
    -(2 ^ 23 : Int) ≤ swapIterationNextTick v a s evm ∧
      swapIterationNextTick v a s evm < 2 ^ 23 := by
  rw [swapIterationNextTick, bitmapNextResult_distance]
  exact normalizeSint_bounds ⟨24, by decide⟩ _

theorem swapIterationFlag_word (masked : UInt256) :
    bitmapNextFlag masked = (decide (masked ≠ ⟨0⟩)).toUInt256 := by
  by_cases hz : masked = ⟨0⟩
  · subst masked; decide
  · rw [bitmapNextFlag, if_neg hz,
      show decide (masked ≠ ⟨0⟩) = true from decide_eq_true hz]
    rfl

theorem swapIterationFlag_clean (masked : UInt256) :
    UInt256.isZero (UInt256.isZero (bitmapNextFlag masked)) =
      (decide (masked ≠ ⟨0⟩)).toUInt256 := by
  rw [swapIterationFlag_word]
  cases decide (masked ≠ ⟨0⟩) <;> rfl

theorem swapIterationBitmapFrame_step (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (s : SwapStateData) (evm : EVM.State) :
    (swapIterationBitmapFrame frame v a s evm).locals.get? "step" =
      some (swapIterationInitial s.price).value := by
  simp only [swapIterationBitmapFrame, swapIterationInputFrame, swapIterationFrame,
    resumeAfterInternalCall, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  rfl

theorem swapIterationBitmapFrame_tuple (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (s : SwapStateData) (evm : EVM.State) :
    (swapIterationBitmapFrame frame v a s evm).locals.get? "__c2" =
      some (.tuple [.int (swapIterationNextTick v a s evm),
        .bool (swapIterationInitialized v a s evm)]) := by
  simp only [swapIterationBitmapFrame, resumeAfterInternalCall,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  rfl

theorem swapIterationBitmapStoresFrame_step (frame : Frame) (d : SwapIterationData)
    (tick : Int) (hit : Bool) :
    (swapIterationBitmapStoresFrame frame d tick hit).locals.get? "step" =
      some {d with tickNext := tick, initialized := hit}.value :=
  Std.HashMap.getElem?_insert_self

theorem swapIterationClampFrame_step {frame : Frame} (d : SwapIterationData)
    (hd : frame.locals.get? "step" = some d.value) :
    (swapIterationClampFrame frame d).locals.get? "step" =
      some {d with tickNext := swapIterationClampTick d.tickNext}.value := by
  unfold swapIterationClampFrame swapIterationClampTick
  split_ifs <;> first | exact Std.HashMap.getElem?_insert_self | exact hd

end Benchmarks.UniswapV3.Pool

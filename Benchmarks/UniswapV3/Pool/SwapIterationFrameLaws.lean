import Benchmarks.UniswapV3.Pool.SwapIterationTickPrefix
import Benchmarks.UniswapV3.Pool.SwapIterationPrice

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapIterationClampFrame_parts (frame : Frame) (d : SwapIterationData) :
    (swapIterationClampFrame frame d).contract = frame.contract ∧
      (swapIterationClampFrame frame d).immutables = frame.immutables := by
  unfold swapIterationClampFrame
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem swapIterationClampFrame_get (frame : Frame) (d : SwapIterationData) (name : Ident)
    (hs : name ≠ "step") :
    (swapIterationClampFrame frame d).locals.get? name = frame.locals.get? name := by
  unfold swapIterationClampFrame
  split_ifs <;> simp only [swapIterationFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, beq_iff_eq, Ne.symm hs, if_false]

theorem swapIterationTickFrame_parts (frame : Frame) (d : SwapIterationData)
    (tick : Int) (hit : Bool) :
    (swapIterationTickFrame frame d tick hit).contract = frame.contract ∧
      (swapIterationTickFrame frame d tick hit).immutables = frame.immutables :=
  swapIterationClampFrame_parts (swapIterationBitmapStoresFrame frame d tick hit)
    {d with tickNext := tick, initialized := hit}

theorem swapIterationClampedFrame_parts (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (s : SwapStateData) (evm : EVM.State) :
    (swapIterationClampedFrame frame v a s evm).contract = frame.contract ∧
      (swapIterationClampedFrame frame v a s evm).immutables = frame.immutables := by
  exact swapIterationTickFrame_parts (swapIterationBitmapFrame frame v a s evm)
    (swapIterationInitial s.price) (swapIterationNextTick v a s evm)
    (swapIterationInitialized v a s evm)

theorem swapIterationClampedFrame_get (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (s : SwapStateData) (evm : EVM.State) (name : Ident)
    (hs : name ≠ "step") (hc : name ≠ "__c2") :
    (swapIterationClampedFrame frame v a s evm).locals.get? name = frame.locals.get? name := by
  rw [swapIterationClampedFrame, swapIterationTickFrame, swapIterationClampFrame_get _ _ _ hs]
  simp only [swapIterationBitmapStoresFrame, swapIterationBitmapFrame,
    swapIterationInputFrame, swapIterationFrame, resumeAfterInternalCall,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_iff_eq,
    Ne.symm hs, Ne.symm hc, if_false]

end Benchmarks.UniswapV3.Pool

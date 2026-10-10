import Benchmarks.UniswapV3.Pool.SwapFeeGrowthSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem swapFeeGrowthFrame_parts (frame : Frame) (s : SwapStateData) (d : SwapIterationData) :
    (swapFeeGrowthFrame frame s d).contract = frame.contract ∧
      (swapFeeGrowthFrame frame s d).immutables = frame.immutables := by
  unfold swapFeeGrowthFrame
  split <;> exact ⟨rfl, rfl⟩

theorem swapFeeGrowthFrame_state {frame : Frame} (s : SwapStateData) (d : SwapIterationData)
    (hs : frame.locals.get? "state" = some s.value) :
    (swapFeeGrowthFrame frame s d).locals.get? "state" = some (swapFeeGrowthState s d).value := by
  unfold swapFeeGrowthFrame swapFeeGrowthState
  split_ifs
  · exact Std.HashMap.getElem?_insert_self
  · exact hs

theorem swapFeeGrowthFrame_get (frame : Frame) (s : SwapStateData) (d : SwapIterationData)
    (name : Ident) (hs : name ≠ "state") (hc : name ≠ "__c11") :
    (swapFeeGrowthFrame frame s d).locals.get? name = frame.locals.get? name := by
  unfold swapFeeGrowthFrame
  split
  · simp only [swapFeeGrowthUpdateFrame, swapStateFrame, swapFeeGrowthCallFrame,
      resumeAfterInternalCall, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, Ne.symm hs, Ne.symm hc, if_false]
  · rfl

end Benchmarks.UniswapV3.Pool

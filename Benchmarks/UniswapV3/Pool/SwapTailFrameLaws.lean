import Benchmarks.UniswapV3.Pool.SwapCrossTickSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem swapStateFrame_get (frame : Frame) (s : SwapStateData) (name : Ident)
    (hn : name ≠ "state") :
    (swapStateFrame frame s).locals.get? name = frame.locals.get? name := by
  simp only [swapStateFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    beq_iff_eq, Ne.symm hn, if_false]

theorem swapPriceChangedFrame_parts (frame : Frame) (s : SwapStateData)
    (d : SwapIterationData) :
    (swapPriceChangedFrame frame s d).contract = frame.contract ∧
    (swapPriceChangedFrame frame s d).immutables = frame.immutables := by
  unfold swapPriceChangedFrame
  split <;> exact ⟨rfl, rfl⟩

theorem swapPriceChangedFrame_state (frame : Frame) (s : SwapStateData)
    (d : SwapIterationData) (hs : frame.locals.get? "state" = some s.value) :
    (swapPriceChangedFrame frame s d).locals.get? "state" =
      some (swapPriceChangedState s d).value := by
  unfold swapPriceChangedFrame swapPriceChangedState
  split
  · exact hs
  · exact Std.HashMap.getElem?_insert_self

theorem swapPriceChangedFrame_get (frame : Frame) (s : SwapStateData)
    (d : SwapIterationData) (name : Ident) (hs : name ≠ "state") (hc : name ≠ "__c15") :
    (swapPriceChangedFrame frame s d).locals.get? name = frame.locals.get? name := by
  unfold swapPriceChangedFrame
  split
  · rfl
  · exact (swapStateFrame_get _ _ name hs).trans
      (resumeAfterInternalCall_get _ "__c15" name _ hc)

end Benchmarks.UniswapV3.Pool

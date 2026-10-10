import Benchmarks.UniswapV3.Pool.SwapProtocolSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem swapProtocolFrame_parts (frame : Frame) (c : SwapCacheData) (s : SwapStateData)
    (d : SwapIterationData) :
    (swapProtocolFrame frame c s d).contract = frame.contract ∧
      (swapProtocolFrame frame c s d).immutables = frame.immutables := by
  unfold swapProtocolFrame
  split <;> exact ⟨rfl, rfl⟩

theorem swapProtocolFrame_state {frame : Frame} (c : SwapCacheData) (s : SwapStateData)
    (d : SwapIterationData) (hs : frame.locals.get? "state" = some s.value) :
    (swapProtocolFrame frame c s d).locals.get? "state" = some (swapProtocolState c s d).value := by
  unfold swapProtocolFrame swapProtocolState
  split_ifs
  · exact Std.HashMap.getElem?_insert_self
  · exact hs

theorem swapProtocolFrame_step {frame : Frame} (c : SwapCacheData) (s : SwapStateData)
    (d : SwapIterationData) (hd : frame.locals.get? "step" = some d.value) :
    (swapProtocolFrame frame c s d).locals.get? "step" = some (swapProtocolData c d).value := by
  unfold swapProtocolFrame swapProtocolData
  split_ifs
  · simp only [swapProtocolUpdateFrame, swapStateFrame, swapProtocolFeeFrame, swapIterationFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  · exact hd

theorem swapProtocolFrame_get (frame : Frame) (c : SwapCacheData) (s : SwapStateData)
    (d : SwapIterationData) (name : Ident)
    (hs : name ≠ "state") (hd : name ≠ "step") (hdelta : name ≠ "delta") :
    (swapProtocolFrame frame c s d).locals.get? name = frame.locals.get? name := by
  unfold swapProtocolFrame
  split
  · simp only [swapProtocolUpdateFrame, swapStateFrame, swapProtocolFeeFrame, swapIterationFrame,
      swapProtocolDeltaFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, Ne.symm hs, Ne.symm hd, Ne.symm hdelta, if_false]
  · rfl

end Benchmarks.UniswapV3.Pool

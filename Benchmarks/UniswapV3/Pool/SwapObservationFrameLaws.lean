import Benchmarks.UniswapV3.Pool.SwapObservationSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem swapObservationFrame_parts (frame : Frame) (c : SwapCacheData)
    (tick : Int) (seconds : UInt256) :
    (swapObservationFrame frame c tick seconds).contract = frame.contract ∧
      (swapObservationFrame frame c tick seconds).immutables = frame.immutables := ⟨rfl, rfl⟩

theorem swapObservationFrame_cache (frame : Frame) (c : SwapCacheData)
    (tick : Int) (seconds : UInt256) :
    (swapObservationFrame frame c tick seconds).locals.get? "cache" =
      some (swapObservationCache c tick seconds).value := Std.HashMap.getElem?_insert_self

theorem swapObservationFrame_get (frame : Frame) (c : SwapCacheData)
    (tick : Int) (seconds : UInt256) (name : Ident)
    (hc : name ≠ "cache") (hr : name ≠ "__c12") :
    (swapObservationFrame frame c tick seconds).locals.get? name = frame.locals.get? name := by
  simp only [swapObservationFrame, swapObservationSecondsFrame, swapObservationTickFrame,
    swapObservationCallFrame, swapCacheFrame, resumeAfterInternalCall,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_iff_eq,
    Ne.symm hc, Ne.symm hr, if_false]

end Benchmarks.UniswapV3.Pool

import Benchmarks.UniswapV3.Pool.SwapAccountingModel
import Benchmarks.UniswapV3.Pool.SourceCallFrames

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem swapAccountingFirstFrame_get (frame : Frame) (exactInput : Bool) (d : SwapIterationData)
    (name : Ident) (hn : name ≠ swapAccountingFirstName exactInput) :
    (swapAccountingFirstFrame frame exactInput d).locals.get? name = frame.locals.get? name :=
  resumeAfterInternalCall_get _ _ _ _ hn

theorem swapAccountingFirstFrame_result (frame : Frame) (exactInput : Bool)
    (d : SwapIterationData) :
    (swapAccountingFirstFrame frame exactInput d).locals.get? (swapAccountingFirstName exactInput) =
      some (.int (Int.ofNat (swapAccountingFirst exactInput d).toNat)) :=
  Std.HashMap.getElem?_insert_self

theorem swapAccountingRemainingFrame_state (frame : Frame) (exactInput : Bool)
    (s : SwapStateData) (d : SwapIterationData) :
    (swapAccountingRemainingFrame frame exactInput s d).locals.get? "state" =
      some {s with remaining := swapAccountingRemaining exactInput s d}.value :=
  Std.HashMap.getElem?_insert_self

theorem swapAccountingRemainingFrame_step {frame : Frame} (exactInput : Bool)
    (s : SwapStateData) (d : SwapIterationData)
    (hd : frame.locals.get? "step" = some d.value) :
    (swapAccountingRemainingFrame frame exactInput s d).locals.get? "step" = some d.value := by
  have hname : "step" ≠ swapAccountingFirstName exactInput := by cases exactInput <;> decide
  have h := (swapAccountingFirstFrame_get frame exactInput d "step" hname).trans hd
  simpa only [swapAccountingRemainingFrame, swapStateFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert] using h

theorem swapAccountingSecondFrame_state (frame : Frame) (exactInput : Bool)
    (s : SwapStateData) (d : SwapIterationData) :
    (swapAccountingSecondFrame frame exactInput s d).locals.get? "state" =
      some {s with remaining := swapAccountingRemaining exactInput s d}.value := by
  exact (resumeAfterInternalCall_get _ _ _ _
    (show "state" ≠ swapAccountingSecondName exactInput by cases exactInput <;> decide)).trans
    (swapAccountingRemainingFrame_state frame exactInput s d)

theorem swapAccountingSecondFrame_result (frame : Frame) (exactInput : Bool)
    (s : SwapStateData) (d : SwapIterationData) :
    (swapAccountingSecondFrame frame exactInput s d).locals.get?
        (swapAccountingSecondName exactInput) =
      some (.int (Int.ofNat (swapAccountingSecond exactInput d).toNat)) :=
  Std.HashMap.getElem?_insert_self

theorem swapAccountingMathFrame_state (frame : Frame) (exactInput : Bool)
    (s : SwapStateData) (d : SwapIterationData) :
    (swapAccountingMathFrame frame exactInput s d).locals.get? "state" =
      some {s with remaining := swapAccountingRemaining exactInput s d}.value := by
  exact (resumeAfterInternalCall_get _ _ _ _
    (show "state" ≠ swapAccountingResultName exactInput by cases exactInput <;> decide)).trans
    (swapAccountingSecondFrame_state frame exactInput s d)

theorem swapAccountingMathFrame_result (frame : Frame) (exactInput : Bool)
    (s : SwapStateData) (d : SwapIterationData) :
    (swapAccountingMathFrame frame exactInput s d).locals.get?
        (swapAccountingResultName exactInput) =
      some (.int (swapAccountingCalculated exactInput s d)) :=
  Std.HashMap.getElem?_insert_self

end Benchmarks.UniswapV3.Pool

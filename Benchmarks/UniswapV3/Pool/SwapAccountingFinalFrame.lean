import Benchmarks.UniswapV3.Pool.SwapAccountingFrameLaws

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem swapAccountingFrame_parts (frame : Frame) (exactInput : Bool)
    (s : SwapStateData) (d : SwapIterationData) :
    (swapAccountingFrame frame exactInput s d).contract = frame.contract ∧
      (swapAccountingFrame frame exactInput s d).immutables = frame.immutables := by
  dsimp only [swapAccountingFrame, swapStateFrame, swapAccountingMathFrame,
    swapAccountingSecondFrame, swapAccountingRemainingFrame, swapAccountingFirstFrame,
    resumeAfterInternalCall]
  exact ⟨rfl, rfl⟩

theorem swapAccountingFrame_state (frame : Frame) (exactInput : Bool)
    (s : SwapStateData) (d : SwapIterationData) :
    (swapAccountingFrame frame exactInput s d).locals.get? "state" =
      some (swapAccountingState exactInput s d).value := Std.HashMap.getElem?_insert_self

theorem swapAccountingFrame_get (frame : Frame) (exactInput : Bool)
    (s : SwapStateData) (d : SwapIterationData) (name : Ident)
    (hs : name ≠ "state") (hfirst : name ≠ swapAccountingFirstName exactInput)
    (hsecond : name ≠ swapAccountingSecondName exactInput)
    (hresult : name ≠ swapAccountingResultName exactInput) :
    (swapAccountingFrame frame exactInput s d).locals.get? name = frame.locals.get? name := by
  simp only [swapAccountingFrame, swapStateFrame, swapAccountingMathFrame,
    swapAccountingSecondFrame, swapAccountingRemainingFrame, swapAccountingFirstFrame,
    resumeAfterInternalCall, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    beq_iff_eq, Ne.symm hs, Ne.symm hfirst, Ne.symm hsecond, Ne.symm hresult, if_false]

theorem swapAccountingFrame_step {frame : Frame} (exactInput : Bool)
    (s : SwapStateData) (d : SwapIterationData)
    (hd : frame.locals.get? "step" = some d.value) :
    (swapAccountingFrame frame exactInput s d).locals.get? "step" = some d.value := by
  exact (swapAccountingFrame_get frame exactInput s d "step" (by decide)
    (by cases exactInput <;> decide) (by cases exactInput <;> decide)
    (by cases exactInput <;> decide)).trans hd

end Benchmarks.UniswapV3.Pool

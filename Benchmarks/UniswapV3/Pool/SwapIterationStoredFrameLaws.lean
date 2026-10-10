import Benchmarks.UniswapV3.Pool.SwapIterationStoredModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapIterationStoredFrame_parts (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (s : SwapStateData) (evm : EVM.State) :
    (swapIterationStoredFrame frame v a s evm).contract = frame.contract ∧
      (swapIterationStoredFrame frame v a s evm).immutables = frame.immutables := by
  dsimp only [swapIterationStoredFrame, swapIterationResultFrame, swapIterationFrame,
    swapStateFrame, swapIterationComputedFrame, swapIterationStepFrame, resumeAfterInternalCall,
    swapIterationPriceFrame, swapIterationSqrtFrame]
  exact swapIterationClampedFrame_parts frame v a s evm

theorem swapIterationStoredFrame_state (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (s : SwapStateData) (evm : EVM.State) :
    (swapIterationStoredFrame frame v a s evm).locals.get? "state" =
      some (swapIterationStoredState v a s evm).value := by
  simp only [swapIterationStoredFrame, swapIterationResultFrame, swapIterationFrame,
    swapStateFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  rfl

theorem swapIterationStoredFrame_step (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (s : SwapStateData) (evm : EVM.State) :
    (swapIterationStoredFrame frame v a s evm).locals.get? "step" =
      some (swapIterationStoredData v a s evm).value :=
  Std.HashMap.getElem?_insert_self

theorem swapIterationStoredFrame_get (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (s : SwapStateData) (evm : EVM.State) (name : Ident)
    (hstate : name ≠ "state") (hstep : name ≠ "step") (hc2 : name ≠ "__c2")
    (hc3 : name ≠ "__c3") (hc4 : name ≠ "__c4") :
    (swapIterationStoredFrame frame v a s evm).locals.get? name = frame.locals.get? name := by
  simp only [swapIterationStoredFrame, swapIterationResultFrame, swapIterationFrame,
    swapStateFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    beq_iff_eq, Ne.symm hstate, Ne.symm hstep, if_false]
  exact swapIterationComputedFrame_get frame v a s evm name hstep hc2 hc3 hc4

end Benchmarks.UniswapV3.Pool

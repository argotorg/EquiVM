import Benchmarks.UniswapV3.Pool.SwapIterationAccountingPrefix
import Benchmarks.UniswapV3.Pool.SwapAccountingFinalFrame

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

theorem swapIterationAccountedFrame_parts (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (s : SwapStateData) (evm : EVM.State) :
    (swapIterationAccountedFrame frame v a s evm).contract = frame.contract ∧
      (swapIterationAccountedFrame frame v a s evm).immutables = frame.immutables := by
  have h1 := swapAccountingFrame_parts (swapIterationStoredFrame frame v a s evm)
    (swapExactInput a) (swapIterationStoredState v a s evm) (swapIterationStoredData v a s evm)
  have h2 := swapIterationStoredFrame_parts frame v a s evm
  exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem swapIterationAccountedFrame_state (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (s : SwapStateData) (evm : EVM.State) :
    (swapIterationAccountedFrame frame v a s evm).locals.get? "state" =
      some (swapIterationAccountedState v a s evm).value :=
  swapAccountingFrame_state (swapIterationStoredFrame frame v a s evm) (swapExactInput a)
    (swapIterationStoredState v a s evm) (swapIterationStoredData v a s evm)

theorem swapIterationAccountedFrame_step (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (s : SwapStateData) (evm : EVM.State) :
    (swapIterationAccountedFrame frame v a s evm).locals.get? "step" =
      some (swapIterationStoredData v a s evm).value :=
  swapAccountingFrame_step (swapExactInput a) (swapIterationStoredState v a s evm)
    (swapIterationStoredData v a s evm) (swapIterationStoredFrame_step frame v a s evm)

theorem swapIterationAccountedFrame_get (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (s : SwapStateData) (evm : EVM.State) (name : Ident)
    (hn : name ∉ ["state", "step", "__c2", "__c3", "__c4", "__c5", "__c6", "__c7",
      "__c8", "__c9", "__c10"]) :
    (swapIterationAccountedFrame frame v a s evm).locals.get? name = frame.locals.get? name := by
  simp only [List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true] at hn
  rcases hn with ⟨hs, ht, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10⟩
  have hfirst : name ≠ swapAccountingFirstName (swapExactInput a) := by
    cases swapExactInput a
    · exact hc8
    · exact hc5
  have hsecond : name ≠ swapAccountingSecondName (swapExactInput a) := by
    cases swapExactInput a
    · exact hc9
    · exact hc6
  have hresult : name ≠ swapAccountingResultName (swapExactInput a) := by
    cases swapExactInput a
    · exact hc10
    · exact hc7
  exact (swapAccountingFrame_get (swapIterationStoredFrame frame v a s evm) (swapExactInput a)
    (swapIterationStoredState v a s evm) (swapIterationStoredData v a s evm) name
    hs hfirst hsecond hresult).trans
    (swapIterationStoredFrame_get frame v a s evm name hs ht hc2 hc3 hc4)

end Benchmarks.UniswapV3.Pool

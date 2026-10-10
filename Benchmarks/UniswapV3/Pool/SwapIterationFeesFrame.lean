import Benchmarks.UniswapV3.Pool.SwapIterationFeesPrefix
import Benchmarks.UniswapV3.Pool.SwapFeeGrowthFrameLaws

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapIterationFeesFrame_parts (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (c : SwapCacheData) (s : SwapStateData) (evm : EVM.State) :
    (swapIterationFeesFrame frame v a c s evm).contract = frame.contract ∧
    (swapIterationFeesFrame frame v a c s evm).immutables = frame.immutables := by
  have h1 := swapIterationAccountedFrame_parts frame v a s evm
  have h2 := swapProtocolFrame_parts (swapIterationAccountedFrame frame v a s evm) c
    (swapIterationAccountedState v a s evm) (swapIterationStoredData v a s evm)
  have h3 := swapFeeGrowthFrame_parts
    (swapProtocolFrame (swapIterationAccountedFrame frame v a s evm) c
      (swapIterationAccountedState v a s evm) (swapIterationStoredData v a s evm))
    (swapProtocolState c (swapIterationAccountedState v a s evm)
      (swapIterationStoredData v a s evm)) (swapProtocolData c (swapIterationStoredData v a s evm))
  exact ⟨h3.1.trans (h2.1.trans h1.1), h3.2.trans (h2.2.trans h1.2)⟩

theorem swapIterationFeesFrame_state (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (c : SwapCacheData) (s : SwapStateData) (evm : EVM.State) :
    (swapIterationFeesFrame frame v a c s evm).locals.get? "state" =
      some (swapIterationFeesState v a c s evm).value :=
  swapFeeGrowthFrame_state _ _ (swapProtocolFrame_state c _ _
    (swapIterationAccountedFrame_state frame v a s evm))

theorem swapIterationFeesFrame_step (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (c : SwapCacheData) (s : SwapStateData) (evm : EVM.State) :
    (swapIterationFeesFrame frame v a c s evm).locals.get? "step" =
      some (swapIterationFeesData v a c s evm).value :=
  (swapFeeGrowthFrame_get _ _ _ "step" (by decide) (by decide)).trans
    (swapProtocolFrame_step c _ _ (swapIterationAccountedFrame_step frame v a s evm))

def swapFeesWrites : List Ident :=
  ["state", "step", "__c2", "__c3", "__c4", "__c5", "__c6", "__c7", "__c8", "__c9",
    "__c10", "delta", "__c11"]

theorem swapIterationFeesFrame_get (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (c : SwapCacheData) (s : SwapStateData) (evm : EVM.State) (name : Ident)
    (hn : name ∉ swapFeesWrites) :
    (swapIterationFeesFrame frame v a c s evm).locals.get? name = frame.locals.get? name := by
  have hns : name ≠ "state" := by intro h; subst name; exact hn (by decide)
  have hnt : name ≠ "step" := by intro h; subst name; exact hn (by decide)
  have hnd : name ≠ "delta" := by intro h; subst name; exact hn (by decide)
  have hnc : name ≠ "__c11" := by intro h; subst name; exact hn (by decide)
  have hnprev : name ∉ ["state", "step", "__c2", "__c3", "__c4", "__c5", "__c6", "__c7",
      "__c8", "__c9", "__c10"] := by
    simp only [swapFeesWrites, List.mem_cons, List.not_mem_nil, not_or,
      not_false_eq_true, and_true] at hn ⊢
    tauto
  exact (swapFeeGrowthFrame_get _ _ _ name hns hnc).trans
    ((swapProtocolFrame_get _ c _ _ name hns hnt hnd).trans
      (swapIterationAccountedFrame_get frame v a s evm name hnprev))

theorem swapProtocolData_unchanged (c : SwapCacheData) (d : SwapIterationData) :
    (swapProtocolData c d).tickNext = d.tickNext ∧
    (swapProtocolData c d).priceStart = d.priceStart ∧
    (swapProtocolData c d).priceNext = d.priceNext := by
  unfold swapProtocolData
  split <;> exact ⟨rfl, rfl, rfl⟩

theorem swapIterationFeesData_bounds (v : UniswapV3PoolImmutables) (a : SwapArgs)
    (c : SwapCacheData) (s : SwapStateData) (evm : EVM.State) (hs : s.Fits) :
    let d := swapIterationFeesData v a c s evm
    (-(2 ^ 23 : Int) ≤ d.tickNext ∧ d.tickNext < 2 ^ 23) ∧
    d.priceStart.toNat < 2 ^ 160 ∧ d.priceNext.toNat < 2 ^ 160 := by
  dsimp only [swapIterationFeesData]
  have hu := swapProtocolData_unchanged c (swapIterationStoredData v a s evm)
  rw [hu.1, hu.2.1, hu.2.2]
  have ht := swapIterationClampedData_bounds v a s evm
  refine ⟨?_, ?_, ?_⟩
  · change -(2 ^ 23 : Int) ≤ (swapIterationClampedData v a s evm).tickNext ∧
      (swapIterationClampedData v a s evm).tickNext < 2 ^ 23
    omega
  · exact hs.2.2.1
  · exact tickSqrtValue_lt160 (swapIterationClampedData v a s evm).tickNext

end Benchmarks.UniswapV3.Pool

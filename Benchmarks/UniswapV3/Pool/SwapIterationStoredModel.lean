import Benchmarks.UniswapV3.Pool.SwapIterationStepPrefix
import Benchmarks.UniswapV3.Pool.SwapIterationResultTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapIterationComputedArgs (v : UniswapV3PoolImmutables) (a : SwapArgs) (s : SwapStateData)
    (evm : EVM.State) : SwapStepArgs :=
  swapIterationStepArgs v a s (swapIterationComputedData v a s evm)

noncomputable def swapIterationStoredState (v : UniswapV3PoolImmutables) (a : SwapArgs)
    (s : SwapStateData) (evm : EVM.State) : SwapStateData :=
  {s with price := swapStepPrice (swapIterationComputedArgs v a s evm)}

noncomputable def swapIterationStoredData (v : UniswapV3PoolImmutables) (a : SwapArgs)
    (s : SwapStateData) (evm : EVM.State) : SwapIterationData :=
  let b := swapIterationComputedArgs v a s evm
  swapIterationResultData (swapIterationComputedData v a s evm)
    (swapStepAmount b true) (swapStepOutput b) (swapStepFee b)

noncomputable def swapIterationStoredFrame (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (s : SwapStateData) (evm : EVM.State) : Frame :=
  let b := swapIterationComputedArgs v a s evm
  swapIterationResultFrame (swapIterationComputedFrame frame v a s evm)
    s (swapIterationComputedData v a s evm)
    (swapStepPrice b) (swapStepAmount b true) (swapStepOutput b) (swapStepFee b)

theorem swapIterationComputedFrame_get (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (s : SwapStateData) (evm : EVM.State) (name : Ident)
    (hs : name ≠ "step") (hc2 : name ≠ "__c2") (hc3 : name ≠ "__c3") (hc4 : name ≠ "__c4") :
    (swapIterationComputedFrame frame v a s evm).locals.get? name = frame.locals.get? name := by
  simp only [swapIterationComputedFrame, swapIterationStepFrame, resumeAfterInternalCall,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_iff_eq, Ne.symm hc4, if_false]
  exact (swapIterationPriceFrame_get _ _ _ hs hc3).trans
    (swapIterationClampedFrame_get _ _ _ _ _ _ hs hc2)

theorem swapIterationComputedFrame_step (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (s : SwapStateData) (evm : EVM.State) :
    (swapIterationComputedFrame frame v a s evm).locals.get? "step" =
      some (swapIterationComputedData v a s evm).value := by
  simpa only [swapIterationComputedFrame, swapIterationStepFrame, resumeAfterInternalCall,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using
    swapIterationPriceFrame_step (swapIterationClampedFrame frame v a s evm)
      (swapIterationClampedData v a s evm)

theorem swapIterationComputedFrame_results (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (s : SwapStateData) (evm : EVM.State) :
    (swapIterationComputedFrame frame v a s evm).locals.get? "__c4" =
      some (.tuple (swapStepResults (swapIterationComputedArgs v a s evm))) :=
  Std.HashMap.getElem?_insert_self

theorem swapIterationStoredState_fits (v : UniswapV3PoolImmutables) (a : SwapArgs)
    (s : SwapStateData) (evm : EVM.State) (ha : a.Fits) (hs : s.Fits)
    (hv : swapStepValid (swapIterationComputedArgs v a s evm)) :
    (swapIterationStoredState v a s evm).Fits := by
  have hb := swapIterationStepArgs_fits v a s (swapIterationComputedData v a s evm)
    ha hs (tickSqrtValue_lt160 _)
  exact ⟨hs.1, hs.2.1, swapStepPrice_fits _ hb hv.1.1, hs.2.2.2⟩

end Benchmarks.UniswapV3.Pool

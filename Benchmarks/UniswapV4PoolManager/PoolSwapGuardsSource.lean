import Benchmarks.UniswapV4PoolManager.PoolSwapModeSource
import Benchmarks.UniswapV4PoolManager.PoolSwapSetupPost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapGuardsResult (f : Frame) (evm : State) (id packed : UInt256)
    (p : PoolSwapParamsWords) (r : PoolSwapResultWords) (fee : UInt256) : ExecResult :=
  if poolSwapModeValid fee p.amountSpecified then
    if p.amountSpecified = ⟨0⟩ then .returned f evm (some (poolSwapReturnValues ⟨0⟩ fee ⟨0⟩ r))
    else if poolSwapLimitValid packed p.priceLimit p.zeroForOne then
      .ok (poolSwapStepInitFrame (poolSwapLimitFrame f packed p.zeroForOne) evm id p.zeroForOne) evm
    else .reverted
  else .reverted

theorem poolSwapGuardsSource {f : Frame} {evm : State} {id packed : UInt256}
    {p : PoolSwapParamsWords} {r : PoolSwapResultWords} {fee protocol : UInt256}
    (h : PoolSwapSetupLocals f id packed p r fee protocol) :
    ExecBlock config f evm ((poolSwapFunction.body.drop 23).take 5)
      (poolSwapGuardsResult f evm id packed p r fee) := by
  have h0 := poolSwapModeSource (evm := evm) h.fee h.params
  unfold poolSwapGuardsResult
  by_cases hm : poolSwapModeValid fee p.amountSpecified
  · rw [if_pos hm] at h0 ⊢
    apply ExecBlock.consNormal h0
    have h1 := poolSwapZeroSource (evm := evm) h.fee h.params h.result
    by_cases hz : p.amountSpecified = ⟨0⟩
    · rw [if_pos hz] at h1 ⊢
      exact ExecBlock.consReturn h1
    · rw [if_neg hz] at h1 ⊢
      apply ExecBlock.consNormal h1
      have h2 := poolSwapLimitSource (evm := evm) h.contract h.params h.slot h.direction
      by_cases hl : poolSwapLimitValid packed p.priceLimit p.zeroForOne
      · rw [if_pos hl] at h2 ⊢
        exact ExecBlock.consNormal h2 (poolSwapStepInitSource h.limit.self h.limit.direction)
      · rw [if_neg hl] at h2 ⊢
        exact ExecBlock.consRevert h2
  · rw [if_neg hm] at h0 ⊢
    exact ExecBlock.consRevert h0

end Benchmarks.UniswapV4PoolManager

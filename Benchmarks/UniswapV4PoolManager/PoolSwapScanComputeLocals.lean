import Benchmarks.UniswapV4PoolManager.PoolSwapLoopLocals
import Benchmarks.UniswapV4PoolManager.PoolSwapScanComputeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

variable {f : Frame} {id : UInt256} {s : PoolSwapStepWords} {r : PoolSwapResultWords}
  {p : PoolSwapParamsWords} {remaining calculated fee protocol amount : UInt256}

theorem PoolSwapLoopLocals.compute_step (h : PoolSwapLoopLocals f id s r p remaining calculated fee protocol amount)
    (next : UInt256) :
    let w := swapStepWord r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee
    PoolSwapLoopLocals (poolSwapComputeFrame f s r p next remaining fee) id
      (poolSwapComputeStep s next w) {r with price := w.next} p remaining calculated fee protocol amount := by
  dsimp only
  have hget := poolSwapComputeFrame_get f s r p next remaining fee
  refine ⟨(poolSwapComputeFrame_contract ..).trans h.contract, poolSwapComputeFrame_step ..,
    poolSwapComputeFrame_result .., ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hget "params" (by decide) (by decide) (by decide) (by decide)).trans h.params
  · exact (hget "self" (by decide) (by decide) (by decide) (by decide)).trans h.self
  · exact (hget "zeroForOne" (by decide) (by decide) (by decide) (by decide)).trans h.direction
  · exact (hget "amountSpecifiedRemaining" (by decide) (by decide) (by decide) (by decide)).trans h.remaining
  · exact (hget "amountCalculated" (by decide) (by decide) (by decide) (by decide)).trans h.calculated
  · exact (hget "swapFee" (by decide) (by decide) (by decide) (by decide)).trans h.fee
  · exact (hget "protocolFee" (by decide) (by decide) (by decide) (by decide)).trans h.protocol
  · exact (hget "amountToProtocol" (by decide) (by decide) (by decide) (by decide)).trans h.amount

theorem PoolSwapLoopLocals.scan_step (h : PoolSwapLoopLocals f id s r p remaining calculated fee protocol amount)
    (evm : State) :
    let scan := poolSwapScanStep s evm id r p
    PoolSwapLoopLocals (tickClampPriceFrame (poolSwapScanFrame f s evm id r p) scan) id
      {scan with tickNext := tickClampWord scan.tickNext} r p remaining calculated fee protocol amount := by
  dsimp only
  have hget := poolSwapScanPriceFrame_get f s evm id r p
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [tickClampPriceFrame, valueLocal_contract, tickClampFrame_contract, poolSwapScanFrame_contract, h.contract]
  · exact (store_get_ne _ _ (by decide : ("__c13" == "step") = false)).trans
      (tickClampFrame_step (poolSwapScanFrame_step f s evm id r p) (poolSwapScanStep_tick_canonical ..))
  · exact (hget "result" (by decide) (by decide) (by decide) (by decide)).trans h.result
  · exact (hget "params" (by decide) (by decide) (by decide) (by decide)).trans h.params
  · exact (hget "self" (by decide) (by decide) (by decide) (by decide)).trans h.self
  · exact (hget "zeroForOne" (by decide) (by decide) (by decide) (by decide)).trans h.direction
  · exact (hget "amountSpecifiedRemaining" (by decide) (by decide) (by decide) (by decide)).trans h.remaining
  · exact (hget "amountCalculated" (by decide) (by decide) (by decide) (by decide)).trans h.calculated
  · exact (hget "swapFee" (by decide) (by decide) (by decide) (by decide)).trans h.fee
  · exact (hget "protocolFee" (by decide) (by decide) (by decide) (by decide)).trans h.protocol
  · exact (hget "amountToProtocol" (by decide) (by decide) (by decide) (by decide)).trans h.amount

end Benchmarks.UniswapV4PoolManager

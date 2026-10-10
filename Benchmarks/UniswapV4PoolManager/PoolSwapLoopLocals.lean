import Benchmarks.UniswapV4PoolManager.PoolSwapAccountingSource
import Benchmarks.UniswapV4PoolManager.PoolSwapTickPost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

structure PoolSwapLoopLocals (f : Frame) (id : UInt256) (s : PoolSwapStepWords) (r : PoolSwapResultWords)
    (p : PoolSwapParamsWords) (remaining calculated fee protocol amount : UInt256) : Prop where
  contract : f.contract = Benchmarks.UniswapV4PoolManager.contract
  step : f.locals.get? "step" = some (poolSwapStepValue s)
  result : f.locals.get? "result" = some (poolSwapResultValue r)
  params : f.locals.get? "params" = some (poolSwapParamsValue p)
  self : f.locals.get? "self" = some (poolRefValue id)
  direction : f.locals.get? "zeroForOne" = some (.bool p.zeroForOne)
  remaining : f.locals.get? "amountSpecifiedRemaining" = some (.int (EVM.signed remaining))
  calculated : f.locals.get? "amountCalculated" = some (.int (EVM.signed calculated))
  fee : f.locals.get? "swapFee" = some (.int (Int.ofNat fee.toNat))
  protocol : f.locals.get? "protocolFee" = some (.int (Int.ofNat protocol.toNat))
  amount : f.locals.get? "amountToProtocol" = some (.int (Int.ofNat amount.toNat))

variable {f : Frame} {id : UInt256} {s : PoolSwapStepWords} {r : PoolSwapResultWords}
  {p : PoolSwapParamsWords} {remaining calculated fee protocol amount : UInt256}

theorem PoolSwapLoopLocals.amount_step (h : PoolSwapLoopLocals f id s r p remaining calculated fee protocol amount) :
    PoolSwapLoopLocals (poolSwapAmountFrame f s p.amountSpecified remaining calculated) id s r p
      (poolSwapRemainingAfter s p.amountSpecified remaining) (poolSwapCalculatedAfter s p.amountSpecified calculated)
      fee protocol amount := by
  have hget := poolSwapAmountFrame_get f s p.amountSpecified remaining calculated
  refine ⟨(poolSwapAmountFrame_contract ..).trans h.contract, ?_, ?_, ?_, ?_, ?_,
    poolSwapAmountFrame_remaining .., poolSwapAmountFrame_calculated .., ?_, ?_, ?_⟩
  · exact (hget "step" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.step
  · exact (hget "result" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.result
  · exact (hget "params" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.params
  · exact (hget "self" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.self
  · exact (hget "zeroForOne" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.direction
  · exact (hget "swapFee" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.fee
  · exact (hget "protocolFee" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.protocol
  · exact (hget "amountToProtocol" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.amount

theorem PoolSwapLoopLocals.protocol_step (h : PoolSwapLoopLocals f id s r p remaining calculated fee protocol amount) :
    PoolSwapLoopLocals (poolSwapProtocolFrame f s fee protocol amount) id (poolSwapProtocolStep s fee protocol) r p
      remaining calculated fee protocol (poolSwapProtocolAmount s fee protocol amount) := by
  have hget := poolSwapProtocolFrame_get f s fee protocol amount
  refine ⟨(poolSwapProtocolFrame_contract ..).trans h.contract, poolSwapProtocolFrame_step h.step ..,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, poolSwapProtocolFrame_amount h.amount ..⟩
  · exact (hget "result" (by decide) (by decide) (by decide)).trans h.result
  · exact (hget "params" (by decide) (by decide) (by decide)).trans h.params
  · exact (hget "self" (by decide) (by decide) (by decide)).trans h.self
  · exact (hget "zeroForOne" (by decide) (by decide) (by decide)).trans h.direction
  · exact (hget "amountSpecifiedRemaining" (by decide) (by decide) (by decide)).trans h.remaining
  · exact (hget "amountCalculated" (by decide) (by decide) (by decide)).trans h.calculated
  · exact (hget "swapFee" (by decide) (by decide) (by decide)).trans h.fee
  · exact (hget "protocolFee" (by decide) (by decide) (by decide)).trans h.protocol

theorem PoolSwapLoopLocals.growth_step (h : PoolSwapLoopLocals f id s r p remaining calculated fee protocol amount) :
    PoolSwapLoopLocals (poolSwapGrowthFrame f s r.liquidity) id (poolSwapGrowthStep s r.liquidity) r p
      remaining calculated fee protocol amount := by
  have hget := poolSwapGrowthFrame_get f s r.liquidity
  refine ⟨(poolSwapGrowthFrame_contract ..).trans h.contract, poolSwapGrowthFrame_step h.step _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hget "result" (by decide) (by decide)).trans h.result
  · exact (hget "params" (by decide) (by decide)).trans h.params
  · exact (hget "self" (by decide) (by decide)).trans h.self
  · exact (hget "zeroForOne" (by decide) (by decide)).trans h.direction
  · exact (hget "amountSpecifiedRemaining" (by decide) (by decide)).trans h.remaining
  · exact (hget "amountCalculated" (by decide) (by decide)).trans h.calculated
  · exact (hget "swapFee" (by decide) (by decide)).trans h.fee
  · exact (hget "protocolFee" (by decide) (by decide)).trans h.protocol
  · exact (hget "amountToProtocol" (by decide) (by decide)).trans h.amount

theorem PoolSwapLoopLocals.tick_step {evm post : State} {ff : Frame}
    (h : PoolSwapLoopLocals f id s r p remaining calculated fee protocol amount)
    (he : poolSwapTickResult f evm id s r p.zeroForOne = .ok ff post) :
    PoolSwapLoopLocals ff id s (poolSwapTickResultWords evm id s r p.zeroForOne) p
      remaining calculated fee protocol amount ∧ post.executionEnv = evm.executionEnv := by
  obtain ⟨hc, henv, hr, hget⟩ := poolSwapTickResult_frames h.result he
  refine ⟨⟨hc.trans h.contract, ?_, hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, henv⟩
  · exact (hget "step" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.step
  · exact (hget "params" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.params
  · exact (hget "self" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.self
  · exact (hget "zeroForOne" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.direction
  · exact (hget "amountSpecifiedRemaining" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.remaining
  · exact (hget "amountCalculated" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.calculated
  · exact (hget "swapFee" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.fee
  · exact (hget "protocolFee" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.protocol
  · exact (hget "amountToProtocol" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.amount

end Benchmarks.UniswapV4PoolManager

import Benchmarks.UniswapV4PoolManager.PoolSwapIterationPost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def PoolSwapSavedLocals (before after : Frame) : Prop :=
  after.locals.get? "slot0Start" = before.locals.get? "slot0Start" ∧
  after.locals.get? "swapDelta" = before.locals.get? "swapDelta"

theorem PoolSwapSavedLocals.refl (f : Frame) : PoolSwapSavedLocals f f := ⟨rfl, rfl⟩

theorem PoolSwapSavedLocals.trans {f1 f2 f3 : Frame} (h1 : PoolSwapSavedLocals f1 f2)
    (h2 : PoolSwapSavedLocals f2 f3) : PoolSwapSavedLocals f1 f3 :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem poolSwapAmountFrame_saved (f : Frame) (s : PoolSwapStepWords) (specified remaining calculated : UInt256) :
    PoolSwapSavedLocals f (poolSwapAmountFrame f s specified remaining calculated) := by
  constructor <;> exact poolSwapAmountFrame_get f s specified remaining calculated _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem poolSwapProtocolFrame_saved (f : Frame) (s : PoolSwapStepWords) (fee protocol amount : UInt256) :
    PoolSwapSavedLocals f (poolSwapProtocolFrame f s fee protocol amount) := by
  constructor <;> exact poolSwapProtocolFrame_get f s fee protocol amount _ (by decide) (by decide) (by decide)

theorem poolSwapGrowthFrame_saved (f : Frame) (s : PoolSwapStepWords) (liquidity : UInt256) :
    PoolSwapSavedLocals f (poolSwapGrowthFrame f s liquidity) := by
  constructor <;> exact poolSwapGrowthFrame_get f s liquidity _ (by decide) (by decide)

theorem poolSwapAccountingFrame_saved (f : Frame) (s : PoolSwapStepWords) (r : PoolSwapResultWords)
    (specified remaining calculated fee protocol amount : UInt256) :
    PoolSwapSavedLocals f (poolSwapAccountingFrame f s r specified remaining calculated fee protocol amount) :=
  ((poolSwapAmountFrame_saved f s specified remaining calculated).trans
    (poolSwapProtocolFrame_saved _ s fee protocol amount)).trans
    (poolSwapGrowthFrame_saved _ (poolSwapProtocolStep s fee protocol) r.liquidity)

theorem poolSwapTickResult_saved {f ff : Frame} {evm post : State} {id : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {zeroForOne : Bool}
    (hr : f.locals.get? "result" = some (poolSwapResultValue r))
    (he : poolSwapTickResult f evm id s r zeroForOne = .ok ff post) : PoolSwapSavedLocals f ff := by
  have hget := (poolSwapTickResult_frames hr he).2.2.2
  constructor <;> exact hget _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem poolSwapAccountingResult_saved {f ff : Frame} {evm post : State} {id : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}
    {remaining calculated fee protocol amount : UInt256}
    (hl : PoolSwapLoopLocals f id s r p remaining calculated fee protocol amount)
    (he : poolSwapAccountingResult f evm id s r p remaining calculated fee protocol amount = .ok ff post) :
    PoolSwapSavedLocals f ff := by
  unfold poolSwapAccountingResult at he
  split at he
  · exact (poolSwapAccountingFrame_saved f s r p.amountSpecified remaining calculated fee protocol amount).trans
      (poolSwapTickResult_saved hl.amount_step.protocol_step.growth_step.result he)
  · cases he

theorem poolSwapComputeFrame_saved (f : Frame) (s : PoolSwapStepWords) (r : PoolSwapResultWords)
    (p : PoolSwapParamsWords) (next remaining fee : UInt256) :
    PoolSwapSavedLocals f (poolSwapComputeFrame f s r p next remaining fee) := by
  constructor <;> exact poolSwapComputeFrame_get f s r p next remaining fee _ (by decide) (by decide) (by decide) (by decide)

theorem poolSwapScanPriceFrame_saved (f : Frame) (s : PoolSwapStepWords) (evm : State) (id : UInt256)
    (r : PoolSwapResultWords) (p : PoolSwapParamsWords) :
    PoolSwapSavedLocals f (tickClampPriceFrame (poolSwapScanFrame f s evm id r p) (poolSwapScanStep s evm id r p)) := by
  constructor <;> exact poolSwapScanPriceFrame_get f s evm id r p _ (by decide) (by decide) (by decide) (by decide)

theorem poolSwapIterationResult_saved {f ff : Frame} {evm post : State} {id : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}
    {remaining calculated fee protocol amount : UInt256}
    (hl : PoolSwapLoopLocals f id s r p remaining calculated fee protocol amount)
    (he : poolSwapIterationResult f evm id s r p remaining calculated fee protocol amount = .ok ff post) :
    PoolSwapSavedLocals f ff := by
  unfold poolSwapIterationResult at he
  dsimp only at he
  split at he
  · have hc := poolSwapAccountingResult_saved ((hl.scan_step evm).compute_step _) he
    exact ((poolSwapScanPriceFrame_saved f s evm id r p).trans (poolSwapComputeFrame_saved ..)).trans hc
  · cases he

end Benchmarks.UniswapV4PoolManager

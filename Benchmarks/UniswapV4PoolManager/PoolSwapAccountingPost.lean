import Benchmarks.UniswapV4PoolManager.PoolSwapLoopLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapAccountingPost {f ff : Frame} {evm post : State} {id : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}
    {remaining calculated fee protocol amount : UInt256}
    (hl : PoolSwapLoopLocals f id s r p remaining calculated fee protocol amount)
    (htc : int24Canonical r.tick) (hnc : int24Canonical s.tickNext) (hliq : r.liquidity.toNat < 2^128)
    (he : poolSwapAccountingResult f evm id s r p remaining calculated fee protocol amount = .ok ff post) :
    let fees := poolSwapAccountingStep s r fee protocol
    let result := poolSwapTickResultWords evm id fees r p.zeroForOne
    PoolSwapLoopLocals ff id fees result p (poolSwapRemainingAfter s p.amountSpecified remaining)
      (poolSwapCalculatedAfter s p.amountSpecified calculated) fee protocol (poolSwapProtocolAmount s fee protocol amount) ∧
    post.executionEnv = evm.executionEnv ∧ result.price = r.price ∧
    int24Canonical result.tick ∧ result.liquidity.toNat < 2^128 := by
  dsimp only
  unfold poolSwapAccountingResult at he
  split at he
  · have hl' := hl.amount_step.protocol_step.growth_step
    have hn : int24Canonical (poolSwapAccountingStep s r fee protocol).tickNext := by
      rw [(poolSwapAccountingStep_fields s r fee protocol).1]
      exact hnc
    obtain ⟨hfinal, henv⟩ := hl'.tick_step he
    have hb := poolSwapTickResult_canonical htc hn hliq he
    exact ⟨hfinal, henv, hb⟩
  · cases he

end Benchmarks.UniswapV4PoolManager

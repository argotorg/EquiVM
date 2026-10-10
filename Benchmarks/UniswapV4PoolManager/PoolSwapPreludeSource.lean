import Benchmarks.UniswapV4PoolManager.PoolSwapFeesSource
import Benchmarks.UniswapV4PoolManager.PoolSwapGuardsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapPreludeFrame (f : Frame) (evm : State) (id : UInt256) (p : PoolSwapParamsWords) : Frame :=
  poolSwapStepInitFrame (poolSwapLimitFrame (poolSwapFeesFrame f evm id p) (poolSlot0Word evm id) p.zeroForOne)
    evm id p.zeroForOne

def poolSwapPreludeResult (f : Frame) (evm : State) (id : UInt256) (p : PoolSwapParamsWords) : ExecResult :=
  if poolSwapLPFeeValid p.lpFeeOverride then
    poolSwapGuardsResult (poolSwapFeesFrame f evm id p) evm id (poolSlot0Word evm id) p
      (poolSwapInitialResult (poolSlot0Word evm id) (poolLiquidityWord evm id)) (poolSwapInitialFee evm id p)
  else .reverted

theorem poolSwapPreludeSource {f : Frame} {evm : State} {id : UInt256} {p : PoolSwapParamsWords}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p)) (hc : p.lpFeeOverride.toNat < 2^24) :
    ExecBlock config f evm (poolSwapFunction.body.take 28) (poolSwapPreludeResult f evm id p) := by
  have h0 := poolSwapFeesSource (evm := evm) hf hs hp hc
  unfold poolSwapPreludeResult
  by_cases hv : poolSwapLPFeeValid p.lpFeeOverride
  · rw [if_pos hv] at h0 ⊢
    exact execBlock_append h0 (poolSwapGuardsSource (poolSwapFeesLocals hf hs hp))
  · rw [if_neg hv] at h0 ⊢
    exact execBlock_reverted_append h0

theorem poolSwapPreludeLocals {f : Frame} {evm : State} {id : UInt256} {p : PoolSwapParamsWords}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p)) :
    PoolSwapSetupLocals (poolSwapPreludeFrame f evm id p) id (poolSlot0Word evm id) p
      (poolSwapInitialResult (poolSlot0Word evm id) (poolLiquidityWord evm id))
      (poolSwapInitialFee evm id p) (poolSwapProtocolWord (poolSlot0Word evm id) p.zeroForOne) :=
  (poolSwapFeesLocals hf hs hp).limit.step_init evm

theorem poolSwapPreludeLoopLocals {f : Frame} {evm : State} {id : UInt256} {p : PoolSwapParamsWords}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p)) :
    PoolSwapLoopLocals (poolSwapPreludeFrame f evm id p) id (poolSwapInitialStep evm id p.zeroForOne)
      (poolSwapInitialResult (poolSlot0Word evm id) (poolLiquidityWord evm id)) p p.amountSpecified ⟨0⟩
      (poolSwapInitialFee evm id p) (poolSwapProtocolWord (poolSlot0Word evm id) p.zeroForOne) ⟨0⟩ :=
  (poolSwapPreludeLocals hf hs hp).to_loop (store_get_self _ _ _)

end Benchmarks.UniswapV4PoolManager

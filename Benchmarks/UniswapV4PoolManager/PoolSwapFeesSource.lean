import Benchmarks.UniswapV4PoolManager.PoolSwapLoadedSource
import Benchmarks.UniswapV4PoolManager.PoolSwapFeeInitSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem PoolSwapSetupLocals.lp_init {f : Frame} {id packed : UInt256} {p : PoolSwapParamsWords}
    {r : PoolSwapResultWords} {fee protocol : UInt256}
    (h : PoolSwapSetupLocals f id packed p r fee protocol) :
    PoolSwapSetupLocals (poolSwapLPInitFrame f packed p.lpFeeOverride) id packed p r fee protocol := by
  apply h.of_get (poolSwapLPInitFrame_contract ..)
    ((poolSwapLPInitFrame_get f packed p.lpFeeOverride "swapFee" (by decide) (by decide) (by decide) (by decide)).trans h.fee)
  intro key hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact poolSwapLPInitFrame_get _ _ _ _ (by decide) (by decide) (by decide) (by decide)

theorem PoolSwapSetupLocals.fee_init {f : Frame} {id packed lpFee : UInt256} {p : PoolSwapParamsWords}
    {r : PoolSwapResultWords} {fee protocol : UInt256}
    (h : PoolSwapSetupLocals f id packed p r fee protocol) :
    PoolSwapSetupLocals (poolSwapFeeInitFrame f protocol lpFee) id packed p r
      (poolSwapEffectiveFee protocol lpFee) protocol := by
  apply h.of_get (poolSwapFeeInitFrame_contract ..) (poolSwapFeeInitFrame_fee ..)
  intro key hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact poolSwapFeeInitFrame_get _ _ _ _ (by decide) (by decide)

def poolSwapInitialFee (evm : State) (id : UInt256) (p : PoolSwapParamsWords) : UInt256 :=
  poolSwapEffectiveFee (poolSwapProtocolWord (poolSlot0Word evm id) p.zeroForOne)
    (poolSwapLPFeeWord (poolSlot0Word evm id) p.lpFeeOverride)

theorem poolSwapInitialFee_bound (evm : State) (id : UInt256) (p : PoolSwapParamsWords) :
    (poolSwapInitialFee evm id p).toNat < 2^24 :=
  poolSwapEffectiveFee_bound _ (poolSwapLPFeeWord_bound _ _)

def poolSwapFeesFrame (f : Frame) (evm : State) (id : UInt256) (p : PoolSwapParamsWords) : Frame :=
  poolSwapFeeInitFrame (poolSwapLPInitFrame (poolSwapLoadedFrame f evm id p) (poolSlot0Word evm id) p.lpFeeOverride)
    (poolSwapProtocolWord (poolSlot0Word evm id) p.zeroForOne)
    (poolSwapLPFeeWord (poolSlot0Word evm id) p.lpFeeOverride)

theorem poolSwapFeesLocals {f : Frame} {evm : State} {id : UInt256} {p : PoolSwapParamsWords}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p)) :
    PoolSwapSetupLocals (poolSwapFeesFrame f evm id p) id (poolSlot0Word evm id) p
      (poolSwapInitialResult (poolSlot0Word evm id) (poolLiquidityWord evm id))
      (poolSwapInitialFee evm id p) (poolSwapProtocolWord (poolSlot0Word evm id) p.zeroForOne) :=
  (poolSwapLoadedLocals hf hs hp).lp_init.fee_init

theorem poolSwapFeesSource {f : Frame} {evm : State} {id : UInt256} {p : PoolSwapParamsWords}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p)) (hc : p.lpFeeOverride.toNat < 2^24) :
    ExecBlock config f evm (poolSwapFunction.body.take 23)
      (if poolSwapLPFeeValid p.lpFeeOverride then .ok (poolSwapFeesFrame f evm id p) evm else .reverted) := by
  have h0 := poolSwapLoadedSource (evm := evm) hf hs hp
  have hloc := poolSwapLoadedLocals (evm := evm) hf hs hp
  have h1 := poolSwapLPInitSource (evm := evm) hloc.contract hloc.params hloc.slot hc
  by_cases hv : poolSwapLPFeeValid p.lpFeeOverride
  · rw [if_pos hv] at h1 ⊢
    have hl := hloc.lp_init
    have h2 := poolSwapFeeInitSource (evm := evm) hl.contract
      (poolSwapProtocolWord_bound _ _) (poolSwapLPFeeWord_bound _ _) hl.protocol
      (poolSwapLPInitFrame_fee ..) hl.fee
    exact execBlock_append h0 (execBlock_append h1 h2)
  · rw [if_neg hv] at h1 ⊢
    exact execBlock_append h0 (execBlock_reverted_append h1)

end Benchmarks.UniswapV4PoolManager

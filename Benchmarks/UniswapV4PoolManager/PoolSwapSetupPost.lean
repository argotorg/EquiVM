import Benchmarks.UniswapV4PoolManager.PoolSwapSetupLocals
import Benchmarks.UniswapV4PoolManager.PoolSwapLimitSource
import Benchmarks.UniswapV4PoolManager.PoolSwapStepInitSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem poolSwapLimitFrame_contract (f : Frame) (packed : UInt256) (zeroForOne : Bool) :
    (poolSwapLimitFrame f packed zeroForOne).contract = f.contract := wordLocal_contract ..

theorem poolSwapStepInitFrame_contract (f : Frame) (evm : State) (id : UInt256) (zeroForOne : Bool) :
    (poolSwapStepInitFrame f evm id zeroForOne).contract = f.contract := by
  simp only [poolSwapStepInitFrame, valueLocal_contract]

theorem poolSwapStepInitFrame_get (f : Frame) (evm : State) (id : UInt256) (zeroForOne : Bool) (key : Ident)
    (hk : ("step" == key) = false) :
    (poolSwapStepInitFrame f evm id zeroForOne).locals.get? key = f.locals.get? key :=
  store_get_ne2 _ _ _ hk hk

theorem PoolSwapSetupLocals.limit {f : Frame} {id packed : UInt256} {p : PoolSwapParamsWords}
    {r : PoolSwapResultWords} {fee protocol : UInt256}
    (h : PoolSwapSetupLocals f id packed p r fee protocol) :
    PoolSwapSetupLocals (poolSwapLimitFrame f packed p.zeroForOne) id packed p r fee protocol := by
  apply h.of_get (poolSwapLimitFrame_contract ..)
    ((poolSwapLimitFrame_get f packed p.zeroForOne "swapFee" (by decide) (by decide)).trans h.fee)
  intro key hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact poolSwapLimitFrame_get _ _ _ _ (by decide) (by decide)

theorem PoolSwapSetupLocals.step_init {f : Frame} {id packed : UInt256} {p : PoolSwapParamsWords}
    {r : PoolSwapResultWords} {fee protocol : UInt256}
    (h : PoolSwapSetupLocals f id packed p r fee protocol) (evm : State) :
    PoolSwapSetupLocals (poolSwapStepInitFrame f evm id p.zeroForOne) id packed p r fee protocol := by
  apply h.of_get (poolSwapStepInitFrame_contract ..)
    ((poolSwapStepInitFrame_get f evm id p.zeroForOne "swapFee" (by decide)).trans h.fee)
  intro key hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact poolSwapStepInitFrame_get _ _ _ _ _ (by decide)

theorem PoolSwapSetupLocals.to_loop {f : Frame} {id packed : UInt256} {p : PoolSwapParamsWords}
    {r : PoolSwapResultWords} {s : PoolSwapStepWords} {fee protocol : UInt256}
    (h : PoolSwapSetupLocals f id packed p r fee protocol)
    (hs : f.locals.get? "step" = some (poolSwapStepValue s)) :
    PoolSwapLoopLocals f id s r p p.amountSpecified ⟨0⟩ fee protocol ⟨0⟩ :=
  ⟨h.contract, hs, h.result, h.params, h.self, h.direction, h.remaining, h.calculated, h.fee, h.protocol, h.amount⟩

end Benchmarks.UniswapV4PoolManager

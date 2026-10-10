import Benchmarks.UniswapV4PoolManager.PoolSwapLoopLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

structure PoolSwapSetupLocals (f : Frame) (id packed : UInt256) (p : PoolSwapParamsWords)
    (r : PoolSwapResultWords) (fee protocol : UInt256) : Prop where
  contract : f.contract = Benchmarks.UniswapV4PoolManager.contract
  self : f.locals.get? "self" = some (poolRefValue id)
  params : f.locals.get? "params" = some (poolSwapParamsValue p)
  slot : f.locals.get? "slot0Start" = some (wordBytes32Value packed)
  direction : f.locals.get? "zeroForOne" = some (.bool p.zeroForOne)
  result : f.locals.get? "result" = some (poolSwapResultValue r)
  remaining : f.locals.get? "amountSpecifiedRemaining" = some (.int (EVM.signed p.amountSpecified))
  calculated : f.locals.get? "amountCalculated" = some (.int 0)
  fee : f.locals.get? "swapFee" = some (.int (Int.ofNat fee.toNat))
  protocol : f.locals.get? "protocolFee" = some (.int (Int.ofNat protocol.toNat))
  amount : f.locals.get? "amountToProtocol" = some (.int 0)
  delta : f.locals.get? "swapDelta" = some (.int 0)

theorem PoolSwapSetupLocals.of_get {f ff : Frame} {id packed : UInt256} {p : PoolSwapParamsWords}
    {r : PoolSwapResultWords} {fee protocol newFee : UInt256}
    (h : PoolSwapSetupLocals f id packed p r fee protocol)
    (hc : ff.contract = f.contract)
    (hf : ff.locals.get? "swapFee" = some (.int (Int.ofNat newFee.toNat)))
    (hget : ∀ key ∈ (["self", "params", "slot0Start", "zeroForOne", "result",
      "amountSpecifiedRemaining", "amountCalculated", "protocolFee", "amountToProtocol", "swapDelta"] : List Ident),
      ff.locals.get? key = f.locals.get? key) :
    PoolSwapSetupLocals ff id packed p r newFee protocol := by
  exact ⟨hc.trans h.contract, (hget "self" (by decide)).trans h.self,
    (hget "params" (by decide)).trans h.params, (hget "slot0Start" (by decide)).trans h.slot,
    (hget "zeroForOne" (by decide)).trans h.direction, (hget "result" (by decide)).trans h.result,
    (hget "amountSpecifiedRemaining" (by decide)).trans h.remaining,
    (hget "amountCalculated" (by decide)).trans h.calculated, hf,
    (hget "protocolFee" (by decide)).trans h.protocol, (hget "amountToProtocol" (by decide)).trans h.amount,
    (hget "swapDelta" (by decide)).trans h.delta⟩

end Benchmarks.UniswapV4PoolManager

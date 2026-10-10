import Benchmarks.UniswapV4PoolManager.PoolSwapAccountingFrame
import Benchmarks.UniswapV4PoolManager.PoolSwapTickSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapAccountingStep (s : PoolSwapStepWords) (r : PoolSwapResultWords) (fee protocol : UInt256) : PoolSwapStepWords :=
  poolSwapGrowthStep (poolSwapProtocolStep s fee protocol) r.liquidity

theorem poolSwapAccountingStep_fields (s : PoolSwapStepWords) (r : PoolSwapResultWords) (fee protocol : UInt256) :
    (poolSwapAccountingStep s r fee protocol).tickNext = s.tickNext ∧
    (poolSwapAccountingStep s r fee protocol).priceNext = s.priceNext ∧
    (poolSwapAccountingStep s r fee protocol).priceStart = s.priceStart := by
  unfold poolSwapAccountingStep poolSwapGrowthStep poolSwapProtocolStep
  split <;> split <;> exact ⟨rfl, rfl, rfl⟩

def poolSwapAccountingFrame (f : Frame) (s : PoolSwapStepWords) (r : PoolSwapResultWords)
    (specified remaining calculated fee protocol amount : UInt256) : Frame :=
  poolSwapGrowthFrame
    (poolSwapProtocolFrame (poolSwapAmountFrame f s specified remaining calculated) s fee protocol amount)
    (poolSwapProtocolStep s fee protocol) r.liquidity

def poolSwapAccountingResult (f : Frame) (evm : State) (id : UInt256) (s : PoolSwapStepWords)
    (r : PoolSwapResultWords) (p : PoolSwapParamsWords) (remaining calculated fee protocol amount : UInt256) : ExecResult :=
  if poolSwapAmountFits s p.amountSpecified calculated then
    poolSwapTickResult (poolSwapAccountingFrame f s r p.amountSpecified remaining calculated fee protocol amount)
      evm id (poolSwapAccountingStep s r fee protocol) r p.zeroForOne
  else .reverted

theorem poolSwapAccountingSource {f : Frame} {evm : State} {id : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}
    {remaining calculated fee protocol amount : UInt256}
    (hf : f.contract = contract)
    (hs : f.locals.get? "step" = some (poolSwapStepValue s))
    (hr : f.locals.get? "result" = some (poolSwapResultValue r))
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p))
    (hself : f.locals.get? "self" = some (poolRefValue id))
    (hz : f.locals.get? "zeroForOne" = some (.bool p.zeroForOne))
    (hrem : f.locals.get? "amountSpecifiedRemaining" = some (.int (EVM.signed remaining)))
    (hcalc : f.locals.get? "amountCalculated" = some (.int (EVM.signed calculated)))
    (hfee : f.locals.get? "swapFee" = some (.int (Int.ofNat fee.toNat)))
    (hprot : f.locals.get? "protocolFee" = some (.int (Int.ofNat protocol.toNat)))
    (ha : f.locals.get? "amountToProtocol" = some (.int (Int.ofNat amount.toNat))) :
    ExecBlock config f evm (poolSwapLoopBody.drop 15)
      (poolSwapAccountingResult f evm id s r p remaining calculated fee protocol amount) := by
  have hfirst := poolSwapAmountSource (evm := evm) hf hs hp hrem hcalc
  unfold poolSwapAccountingResult
  by_cases hfit : poolSwapAmountFits s p.amountSpecified calculated
  · rw [if_pos hfit] at hfirst ⊢
    let f1 := poolSwapAmountFrame f s p.amountSpecified remaining calculated
    let f2 := poolSwapProtocolFrame f1 s fee protocol amount
    let s2 := poolSwapProtocolStep s fee protocol
    let f3 := poolSwapGrowthFrame f2 s2 r.liquidity
    have hget1 := poolSwapAmountFrame_get f s p.amountSpecified remaining calculated
    have hf1 : f1.contract = contract := (poolSwapAmountFrame_contract ..).trans hf
    have hs1 : f1.locals.get? "step" = some (poolSwapStepValue s) :=
      (hget1 "step" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs
    have hr1 : f1.locals.get? "result" = some (poolSwapResultValue r) :=
      (hget1 "result" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr
    have hfees := poolSwapFeeSource (evm := evm) hf1 hs1 hr1
      ((hget1 "swapFee" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfee)
      ((hget1 "protocolFee" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hprot)
      ((hget1 "amountToProtocol" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha)
    have hf3 : f3.contract = contract :=
      (poolSwapGrowthFrame_contract ..).trans ((poolSwapProtocolFrame_contract ..).trans hf1)
    have hs3 : f3.locals.get? "step" = some (poolSwapStepValue (poolSwapAccountingStep s r fee protocol)) :=
      poolSwapGrowthFrame_step (poolSwapProtocolFrame_step hs1 fee protocol amount) r.liquidity
    have hget3 (key : Ident) (hc20 : ("__c20" == key) = false)
        (hstep : ("step" == key) = false) (hd : ("delta" == key) = false)
        (hamount : ("amountToProtocol" == key) = false) : f3.locals.get? key = f1.locals.get? key :=
      (poolSwapGrowthFrame_get f2 s2 r.liquidity key hc20 hstep).trans
        (poolSwapProtocolFrame_get f1 s fee protocol amount key hd hstep hamount)
    have htick := poolSwapTickSource (evm := evm) (s := poolSwapAccountingStep s r fee protocol) hf3 hs3
      ((hget3 "result" (by decide) (by decide) (by decide) (by decide)).trans hr1)
      ((hget3 "self" (by decide) (by decide) (by decide) (by decide)).trans
        ((hget1 "self" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hself))
      ((hget3 "zeroForOne" (by decide) (by decide) (by decide) (by decide)).trans
        ((hget1 "zeroForOne" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hz))
    exact ExecBlock.consNormal hfirst (execBlock_append hfees (execBlock_singleton htick))
  · rw [if_neg hfit] at hfirst ⊢
    exact ExecBlock.consRevert hfirst

end Benchmarks.UniswapV4PoolManager
